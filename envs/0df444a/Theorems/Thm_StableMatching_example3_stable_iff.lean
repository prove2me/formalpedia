-- Prove2me | Theorems.Thm_StableMatching_example3_stable_iff
-- name    : StableMatching.example3_stable_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:44:43.037618+00:00
-- url     : https://prove2.me/theorems/71f456da-dbf8-47a2-be93-f250e3abb8de
-- title:
--   The 3×3 example has exactly three stable matchings
-- statement:
--   For the instance with men $A,B,C$ and women $X,Y,Z$ and preferences $A: YXZ$, $B: ZYX$, $C: XZY$, $X: BAC$, $Y: CBA$, $Z: ACB$, a matching is stable if and only if it is one of $(AY, BZ, CX)$, $(AX, BY, CZ)$, $(AZ, BX, CY)$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem example3_stable_iff (μ : Matching 3) :
    example3.IsStable μ ↔
      (⇑μ = ![1, 2, 0] ∨ ⇑μ = ![0, 1, 2] ∨ ⇑μ = ![2, 0, 1]) := by sorry

end StableMatching
