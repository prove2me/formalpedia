-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_maxCut_polyReducible_deviation
-- name    : ProjSchedTW.Complexity.maxCut_polyReducible_deviation
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:40:03.340384+00:00
-- url     : https://prove2.me/theorems/b8ac943a-a8e0-4761-bed9-f99e8fb540c3
-- title:
--   Polynomial-Time Reduction from Simple Max Cut to Start-Time Deviation Scheduling
-- statement:
--   The $\text{SIMPLE MAX CUT}$ language ($\text{maxCutLang}$) is polynomial-time many-one reducible to the start-time deviation decision language $\text{deviationLang}$ ($PS\infty \mid \text{temp}, \bar{d} \mid -\sum\sum w_{ij}|S_j - S_i|$, Proposition 3.4.2, p. 241).
-- source:
--   Neumann, Schwindt & Zimmermann (2003), Project Scheduling with Time Windows and Scarce Resources, Proposition 3.4.2, p. 241

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_TimeConstrained

namespace ProjSchedTW.Complexity

theorem maxCut_polyReducible_deviation :
    CookPvsNP.PolyReducible maxCutLang deviationLang := by sorry

end ProjSchedTW.Complexity
