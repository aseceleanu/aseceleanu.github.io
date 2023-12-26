---
permalink: /
title: "Alexandra Seceleanu"
excerpt: "About me"
author_profile: true
redirect_from: 
  - /about/
  - /about.html
---

I am an associate professor of mathematics at the University of Nebraska-Lincoln. My research focuses on commutative algebra with a geometric and computational flavor.

I have been awarded the 2018 [Harold & Esther Edgerton Junior Faculty Award](https://executivevc.unl.edu/faculty/evaluation-recognition/awards/edgerton) for creative research, extraordinary teaching abilities, and academic promise.

I co-organize the workshops[ Women in Commutative Algebra II](https://mathstat.dal.ca/~faridi/WICAII) at CIRM Trento on October 16-20, 2023 and [Women in Commutative Algebra III](https://mathstat.dal.ca/~faridi/WICAIII) at CMO Oaxaca June 2-7, 2024.

In the news: [When life gives you lemons, make mathematicians](https://www.ams.org/journals/notices/202103/rnoti-p375.pdf], an article in the Notices of the AMS about the Polymath program - a large scale online REU I mentor.

My Students
========

Graduate students:
----------------
1.  Ben Drabkin - PhD 2020
2. Andrew Conner - MA 2020
3. Erica Hopkins (co-advised with Mark Walker) - PhD 2021
4. Michael DeBellevue (co-advised with Mark Walker) - PhD 2022
5. Shah Roshan Zamir - Ben Carse Noltig award (2021-2022)
6. Juliann Geraci - Don Miller Outstanding GTA award (2022-2023)
</ul>

Undergraduate students:
------------------
1. Joey Becker ? Chair?s prize for best graduating math major (2015)
2. Diana (Xuehua) Zhong - graduate student at North Carolina State University (since 2018)
3. Helen Holand - honors thesis in progress.


Undergraduate Activities
======

Videos from Selected Talks
======


Site-wide configuration
------
The main configuration file for the site is in the base directory in [_config.yml](https://github.com/academicpages/academicpages.github.io/blob/master/_config.yml), which defines the content in the sidebars and other site-wide features. You will need to replace the default variables with ones about yourself and your site's github repository. The configuration file for the top menu is in [_data/navigation.yml](https://github.com/academicpages/academicpages.github.io/blob/master/_data/navigation.yml). For example, if you don't have a portfolio or blog posts, you can remove those items from that navigation.yml file to remove them from the header. 

Create content & metadata
------
For site content, there is one markdown file for each type of content, which are stored in directories like _publications, _talks, _posts, _teaching, or _pages. For example, each talk is a markdown file in the [_talks directory](https://github.com/academicpages/academicpages.github.io/tree/master/_talks). At the top of each markdown file is structured data in YAML about the talk, which the theme will parse to do lots of cool stuff. The same structured data about a talk is used to generate the list of talks on the [Talks page](https://academicpages.github.io/talks), each [individual page](https://academicpages.github.io/talks/2012-03-01-talk-1) for specific talks, the talks section for the [CV page](https://academicpages.github.io/cv), and the [map of places you've given a talk](https://academicpages.github.io/talkmap.html) (if you run this [python file](https://github.com/academicpages/academicpages.github.io/blob/master/talkmap.py) or [Jupyter notebook](https://github.com/academicpages/academicpages.github.io/blob/master/talkmap.ipynb), which creates the HTML for the map based on the contents of the _talks directory).

**Markdown generator**

I have also created [a set of Jupyter notebooks](https://github.com/academicpages/academicpages.github.io/tree/master/markdown_generator
) that converts a CSV containing structured data about talks or presentations into individual markdown files that will be properly formatted for the academicpages template. The sample CSVs in that directory are the ones I used to create my own personal website at stuartgeiger.com. My usual workflow is that I keep a spreadsheet of my publications and talks, then run the code in these notebooks to generate the markdown files, then commit and push them to the GitHub repository.

How to edit your site's GitHub repository
------
Many people use a git client to create files on their local computer and then push them to GitHub's servers. If you are not familiar with git, you can directly edit these configuration and markdown files directly in the github.com interface. Navigate to a file (like [this one](https://github.com/academicpages/academicpages.github.io/blob/master/_talks/2012-03-01-talk-1.md) and click the pencil icon in the top right of the content preview (to the right of the "Raw | Blame | History" buttons). You can delete a file by clicking the trashcan icon to the right of the pencil icon. You can also create new files or upload files by navigating to a directory and clicking the "Create new file" or "Upload files" buttons. 

Example: editing a markdown file for a talk
![Editing a markdown file for a talk](/images/editing-talk.png)

For more info
------
More info about configuring academicpages can be found in [the guide](https://academicpages.github.io/markdown/). The [guides for the Minimal Mistakes theme](https://mmistakes.github.io/minimal-mistakes/docs/configuration/) (which this theme was forked from) might also be helpful.
