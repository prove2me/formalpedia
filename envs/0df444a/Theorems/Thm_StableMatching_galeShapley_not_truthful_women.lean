-- Prove2me | Theorems.Thm_StableMatching_galeShapley_not_truthful_women
-- name    : StableMatching.galeShapley_not_truthful_women
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:44:17.276443+00:00
-- url     : https://prove2.me/theorems/0bf5bb7d-8fc4-4997-b2dc-ec4b9626864c
-- title:
--   Gale–Shapley is not truthful for women
-- statement:
--   There exist $n$, instances $I$ and $I'$ with $n$ men and $n$ women, and a woman $w$ such that $I'$ differs from $I$ only in $w$'s preference list and, with $\mu$, $\mu'$ the Gale–Shapley outcomes of $I$, $I'$, woman $w$ strictly prefers (according to her true list in $I$) her partner $\mu'^{-1}(w)$ to $\mu^{-1}(w)$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_not_truthful_women :
    ∃ (n : ℕ) (I I' : Instance n) (w : Fin n) (μ μ' : Matching n),
      I.WomanDeviation I' w ∧ I.IsGSOutcome μ ∧ I'.IsGSOutcome μ' ∧
      I.womanPrefers w (μ'.symm w) (μ.symm w) := by sorry

end StableMatching
