-- Prove2me | Theorems.Thm_UnderstandingML_induced_permutation_maximizes
-- name    : UnderstandingML.induced_permutation_maximizes
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:53:55.133362+00:00
-- url     : https://prove2.me/theorems/6cf7f232-e293-49b8-a84a-d7ad80084dcb
-- title:
--   Equation (17.7) / Exercise 17.4: the permutation induced by sorting y maximizes ∑ᵢ vᵢyᵢ over permutation vectors v
-- statement:
--   **Equation (17.7).** Let $V$ be the set of all permutations of $[r]$ encoded as vectors. Then $\pi(y') = \operatorname{argmax}_{v \in V}\sum_{i=1}^r v_i y'_i$.
--
--   Formally (the rearrangement inequality): for every permutation $\sigma$ that orders the indices as $y$ does (monovariance) and every permutation $\tau$, $\sum_i \tau(i)\,y_i \le \sum_i \sigma(i)\,y_i$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §17.4.1 p. 241, Equation (17.7) and Exercise 17.4 p. 247

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Equation (17.7)** (p. 241, Exercise 17.4). The permutation `π(y)` induced by sorting `y`
maximizes `∑ᵢ vᵢ yᵢ` over all permutation vectors `v`: for every permutation `σ` that orders
the indices as `y` does (`σ` monovaries with `y`) and every permutation `τ`,
`∑ᵢ τ(i) yᵢ ≤ ∑ᵢ σ(i) yᵢ` (the rearrangement inequality). -/
theorem induced_permutation_maximizes {r : ℕ} (y : Fin r → ℝ) (σ : Equiv.Perm (Fin r))
    (hσ : Monovary (fun i ↦ ((σ i : ℕ) : ℝ)) y) (τ : Equiv.Perm (Fin r)) :
    ∑ i, ((τ i : ℕ) : ℝ) * y i ≤ ∑ i, ((σ i : ℕ) : ℝ) * y i := by sorry

end UnderstandingML
