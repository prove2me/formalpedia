-- Prove2me | Theorems.Thm_UnderstandingML_soft_svm_norm_bound
-- name    : UnderstandingML.soft_svm_norm_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:40:12.467633+00:00
-- url     : https://prove2.me/theorems/ae207c5d-0e75-405f-b1bd-df1c51f05eed
-- title:
--   Corollary 15.7 (last part): with λ = √(2ρ²/(B²m)), E_S[L^{0−1}_D(A(S))] ≤ E_S[L^hinge_D(A(S))] ≤ min_{‖w‖≤B} L^hinge_D(w) + √(8ρ²B²/m)
-- statement:
--   **Corollary 15.7** (last part). For every $B > 0$, if we set $\lambda = \sqrt{\frac{2\rho^2}{B^2 m}}$ then
--   $$\mathbb{E}_{S \sim D^m}[L^{0-1}_D(A(S))] \le \mathbb{E}_{S \sim D^m}[L^{hinge}_D(A(S))] \le \min_{w : \|w\| \le B} L^{hinge}_D(w) + \sqrt{\frac{8\rho^2 B^2}{m}}.$$
--
--   Formally: the Soft-SVM parameter depends on $m$; "$\min$" is "for every $w$ with $\|w\| \le B$".
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.2.1 p. 208, Corollary 15.7 (from Corollary 13.9)

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 15.7** (p. 208), last part. For every `B > 0`, if Soft-SVM (15.6) is run with
`λ = √(2ρ²/(B²m))` then
`E_S[L^{0−1}_D(A(S))] ≤ E_S[L^hinge_D(A(S))] ≤ min_{w : ‖w‖ ≤ B} L^hinge_D(w) + √(8ρ²B²/m)`.
The parameter depends on `m`; "`min`" is "for every `w` with `‖w‖ ≤ B`". -/
theorem soft_svm_norm_bound {d : ℕ} (D : Measure (Vec d × ℝ)) [IsProbabilityMeasure D]
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (hD : ∀ᵐ z ∂D, ‖z.1‖ ≤ ρ ∧ (z.2 = 1 ∨ z.2 = -1))
    (A : Learner (Vec d × ℝ) (Vec d))
    (hA : ∀ (m : ℕ) (S : Fin m → Vec d × ℝ),
      IsRLM hingeLoss (Real.sqrt (2 * ρ ^ 2 / (B ^ 2 * m))) S (A m S))
    (hAmeas : ∀ m, Measurable (A m)) (m : ℕ) (hm : 0 < m) :
    ∫ S, risk zeroOneLoss D (A m S) ∂(iidLaw D m) ≤
        ∫ S, risk hingeLoss D (A m S) ∂(iidLaw D m) ∧
    ∀ w : Vec d, ‖w‖ ≤ B →
      ∫ S, risk hingeLoss D (A m S) ∂(iidLaw D m) ≤
        risk hingeLoss D w + Real.sqrt (8 * ρ ^ 2 * B ^ 2 / m) := by sorry

end UnderstandingML
