-- Prove2me | Theorems.Thm_TalagrandConc_TSP_tour_insertion
-- name    : TalagrandConc.TSP.tour_insertion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:48.272977+00:00
-- url     : https://prove2.me/theorems/db61b97a-b800-4a94-95f7-5a2c60be03c0
-- title:
--   Proposition 11.2.5 — insertion of omitted sample points
-- statement:
--   Let $X_1,\ldots,X_N$ be points of the unit square and let $J\subseteq\{1,\ldots,N\}$. Suppose $t\ge1$ is in the section's range $t\le\sqrt N/K_0$, and $k_1$ is selected as in Proposition 11.1.4. Given constants $K_1,K_2>0$, assume
--   $$\sum_{i\notin J}\alpha(X_i)\le K_1t,\qquad |\mathcal H_{k_1-1}|\le K_2\frac{2^{2k_1}t^2}{N}.$$
--   Here $\mathcal H_{k_1-1}$ is the set of sparse dyadic squares at level $k_1-1$. Then for a constant $K'>0$ depending only on $K_1,K_2$ and the fixed tour-regularity constant,
--   $$T(\{X_1,\ldots,X_N\})\le T(\{X_i:i\in J\})+K't.$$
--
--   The deterministic estimate limits the extra tour length incurred by inserting the omitted points.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), pp. 176–177, Proposition 11.2.5, Eqs. (11.2.4)–(11.2.6)

import Mathlib
import Definitions.Def_TalagrandConc_TSP_Basic

namespace TalagrandConc.TSP

/-- Talagrand (1995), Proposition 11.2.5, pp. 176–177. -/
theorem tour_insertion :
    ∃ Kbase : ℝ, 0 < Kbase ∧ ∀ K₁ K₂ : ℝ, 0 < K₁ → 0 < K₂ →
      ∃ K' : ℝ, 0 < K' ∧ ∀ (N : ℕ) (t : ℝ) (x : Fin N → Point)
        (J : Finset (Fin N)), 0 < N → 1 ≤ t →
        t ≤ Real.sqrt N / Kbase →
        (∑ i ∈ Jᶜ, alpha N t (sampleSet x) (x i)) ≤ K₁ * t →
        (holeCount N (sampleSet x) (k1 N t - 1) : ℝ) ≤
          K₂ * (2 : ℝ) ^ (2 * k1 N t) * t ^ 2 / N →
        tourLength (sampleSet x) ≤
          tourLength (Finset.univ.image (fun i : J => x i.1)) + K' * t := by sorry

end TalagrandConc.TSP
