-- Prove2me | Theorems.Thm_StableMatching_galeShapley_man_optimal
-- name    : StableMatching.galeShapley_man_optimal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:34:24.422817+00:00
-- url     : https://prove2.me/theorems/870697b6-5d6c-4fc4-8132-17dd98c1fb01
-- title:
--   Gale–Shapley outcome is man-optimal
-- statement:
--   Let $\mu_0$ be the Gale–Shapley outcome of an instance and let $\mu$ be any stable matching of the same instance. Then every man $m$ weakly prefers his Gale–Shapley partner: $\mathrm{manRank}_m(\mu_0(m)) \le \mathrm{manRank}_m(\mu(m))$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_man_optimal {n : ℕ} (I : Instance n) (μ₀ μ : Matching n)
    (h₀ : I.IsGSOutcome μ₀) (hμ : I.IsStable μ) (m : Fin n) :
    I.manRank m (μ₀ m) ≤ I.manRank m (μ m) := by sorry

end StableMatching
