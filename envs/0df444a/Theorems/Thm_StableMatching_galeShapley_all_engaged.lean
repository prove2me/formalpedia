-- Prove2me | Theorems.Thm_StableMatching_galeShapley_all_engaged
-- name    : StableMatching.galeShapley_all_engaged
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:32:09.242672+00:00
-- url     : https://prove2.me/theorems/f2579e1b-5590-45c0-acbd-b9d16dd6c38c
-- title:
--   Gale–Shapley terminates within n² rounds
-- statement:
--   For every instance with $n$ men and $n$ women, after $n^2$ rounds of the Gale–Shapley algorithm every man is engaged (to some woman).
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_all_engaged {n : ℕ} (I : Instance n) :
    ∀ m : Fin n, (I.gsRun (n ^ 2)).IsEngaged m := by sorry

end StableMatching
