-- Prove2me | Theorems.Thm_UnderstandingML_convex_lipschitz_bounded_learnable
-- name    : UnderstandingML.convex_lipschitz_bounded_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:17:52.172245+00:00
-- url     : https://prove2.me/theorems/fb101225-a789-4d28-b08c-014999d583db
-- title:
--   Corollary 13.9: a convex-Lipschitz-bounded problem (ρ, B) is learned by RLM with λ = √(2ρ²/(B²m)): E_S[L_D(A(S))] ≤ min_{w∈H} L_D(w) + ρB√(8/m), hence ≤ +ε for m ≥ 8ρ²B²/ε²
-- statement:
--   **Corollary 13.9.** Let $(H, Z, \ell)$ be a convex-Lipschitz-bounded learning problem with parameters $\rho, B$. For any training set size $m$, let $\lambda = \sqrt{\frac{2\rho^2}{B^2 m}}$. Then the RLM rule with the regularization function $\lambda\|w\|^2$ satisfies
--   $$\mathbb{E}_S[L_D(A(S))] \le \min_{w \in H} L_D(w) + \rho B\sqrt{\frac8m}.$$
--   In particular, for every $\epsilon > 0$, if $m \ge \frac{8\rho^2 B^2}{\epsilon^2}$ then for every distribution $D$, $\mathbb{E}_S[L_D(A(S))] \le \min_{w \in H} L_D(w) + \epsilon$.
--
--   Formally: the RLM learner uses the parameter $\lambda(m)$; "$\min_{w \in H}$" is "for every $w \in H$"; $\rho, B > 0$. Measurability: jointly measurable loss and measurable algorithm, with a nonnegative loss bounded at the origin so that all expectations exist (for the RLM rule the minimizer is unique, so measurability of the algorithm is automatic).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §13.4 p. 179, Corollary 13.9 (from Corollary 13.8)

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 13.9** (p. 179). Let `(H, Z, ℓ)` be a convex-Lipschitz-bounded learning problem
with parameters `ρ, B`. For any training set size `m`, let `λ = √(2ρ²/(B²m))`. Then the RLM rule
with the regularization function `λ‖w‖²` satisfies
`E_S[L_D(A(S))] ≤ min_{w ∈ H} L_D(w) + ρB√(8/m)`. In particular, for every `ε > 0`, if
`m ≥ 8ρ²B²/ε²` then for every distribution `D`, `E_S[L_D(A(S))] ≤ min_{w ∈ H} L_D(w) + ε`.
The RLM parameter depends on `m`; "`min`" is stated as "for every `w ∈ H`". Measurability as in
Corollary 13.6. -/
theorem convex_lipschitz_bounded_learnable {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (H : Set (Vec d)) (loss : Vec d → Z → ℝ) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hprob : ConvexLipschitzBounded H loss ρ B) (A : Learner Z (Vec d))
    (hA : ∀ (m : ℕ) (S : Fin m → Z), IsRLM loss (Real.sqrt (2 * ρ ^ 2 / (B ^ 2 * m))) S (A m S))
    (hmeas : Measurable (Function.uncurry loss)) (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ}
    (hC : ∀ z, loss 0 z ≤ C) (hAmeas : ∀ m, Measurable (A m)) :
    (∀ (D : Measure Z), IsProbabilityMeasure D → ∀ m : ℕ, 0 < m → ∀ w ∈ H,
        ∫ S, risk loss D (A m S) ∂(iidLaw D m) ≤ risk loss D w + ρ * B * Real.sqrt (8 / m)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, 8 * ρ ^ 2 * B ^ 2 / ε ^ 2 ≤ m →
      ∀ (D : Measure Z), IsProbabilityMeasure D → ∀ w ∈ H,
        ∫ S, risk loss D (A m S) ∂(iidLaw D m) ≤ risk loss D w + ε := by sorry

end UnderstandingML
