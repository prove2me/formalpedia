-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_minDelayAlt_npComplete
-- name    : ProjSchedTW.Complexity.minDelayAlt_npComplete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:10:22.973786+00:00
-- url     : https://prove2.me/theorems/46be4d29-dd7b-48a1-aa8e-583b0354a49e
-- title:
--   Proposition 2.5.4 — deciding whether a minimal delaying alternative contains j* is NP-complete
-- statement:
--   Assume that SUBSET SUM is NP-complete (Karp, 1972; Garey and Johnson, 1979). Then the following problem is NP-complete: given resource data $(r_{ik})$, $(R_k)$ of a project with renewable resources, a forbidden set $F$ and an activity $j^*\in F$, is there a minimal delaying alternative $B$ for $F$ with $j^*\in B$?
--   $$L_{\mathrm{MDA}}=\{\langle r,R,F,j^*\rangle:\ \exists B\text{ minimal delaying alternative for }F,\ j^*\in B\}\ \text{is NP-complete}.$$
--
--   Enumerating minimal delaying alternatives is the branching step of the branch-and-bound procedure of §2.5; the proposition says that even deciding whether a given activity can be delayed in some minimal way is hard.
--
--   **Formalization Note** NP-completeness is `CookPvsNP.NPComplete`. The NP-completeness of SUBSET SUM is a hypothesis (Karp's theorem, not a result of the book). Instances must satisfy the book's standing assumptions $n\ge1$, $r_{0k}=r_{n+1,k}=0$, $r_{ik}\le R_k$, and $F$ must be forbidden with $j^*\in F$; codes are binary.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 48, Proposition 2.5.4 and its proof; SUBSET SUM after Garey & Johnson, Computers and Intractability, 1979

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives

namespace ProjSchedTW.Complexity

/-- Proposition 2.5.4 (p. 48), relative to the NP-completeness of SUBSET SUM: testing whether,
for a given forbidden set `F` and activity `j* ∈ F`, some minimal delaying alternative for `F`
contains `j*` is NP-complete. -/
theorem minDelayAlt_npComplete (hSubsetSum : CookPvsNP.NPComplete subsetSumLang) :
    CookPvsNP.NPComplete minDelayAltLang := by sorry

end ProjSchedTW.Complexity
