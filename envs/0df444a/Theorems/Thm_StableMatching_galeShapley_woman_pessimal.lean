-- Prove2me | Theorems.Thm_StableMatching_galeShapley_woman_pessimal
-- name    : StableMatching.galeShapley_woman_pessimal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:35:55.028086+00:00
-- url     : https://prove2.me/theorems/9ab79063-616a-4238-8707-ba3aac638ec6
-- title:
--   Gale–Shapley outcome is woman-pessimal
-- statement:
--   Let $\mu_0$ be the Gale–Shapley outcome of an instance and let $\mu$ be any stable matching of the same instance. Then every woman $w$ weakly prefers her partner in $\mu$ to her Gale–Shapley partner: $\mathrm{womanRank}_w(\mu^{-1}(w)) \le \mathrm{womanRank}_w(\mu_0^{-1}(w))$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_woman_pessimal {n : ℕ} (I : Instance n) (μ₀ μ : Matching n)
    (h₀ : I.IsGSOutcome μ₀) (hμ : I.IsStable μ) (w : Fin n) :
    I.womanRank w (μ.symm w) ≤ I.womanRank w (μ₀.symm w) := by sorry

end StableMatching
