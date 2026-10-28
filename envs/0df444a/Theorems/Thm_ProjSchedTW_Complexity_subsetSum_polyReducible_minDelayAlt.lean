-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_subsetSum_polyReducible_minDelayAlt
-- name    : ProjSchedTW.Complexity.subsetSum_polyReducible_minDelayAlt
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:39:53.78443+00:00
-- url     : https://prove2.me/theorems/48a64a5e-8967-4285-82ff-f1a9c36f2f0a
-- title:
--   Polynomial-Time Reduction from Subset Sum to Min-Delaying-Alternative
-- statement:
--   The $\text{SUBSET SUM}$ language ($\text{subsetSumLang}$) is polynomial-time many-one reducible to $\text{minDelayAltLang}$ via the single-resource construction of Proposition 2.5.4 (p. 48).
-- source:
--   Neumann, Schwindt & Zimmermann (2003), Project Scheduling with Time Windows and Scarce Resources, Proposition 2.5.4, p. 48

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives

namespace ProjSchedTW.Complexity

theorem subsetSum_polyReducible_minDelayAlt :
    CookPvsNP.PolyReducible subsetSumLang minDelayAltLang := by sorry

end ProjSchedTW.Complexity
