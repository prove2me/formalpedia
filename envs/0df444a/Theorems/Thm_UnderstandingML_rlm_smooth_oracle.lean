-- Prove2me | Theorems.Thm_UnderstandingML_rlm_smooth_oracle
-- name    : UnderstandingML.rlm_smooth_oracle
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:18:14.267051+00:00
-- url     : https://prove2.me/theorems/3fc8fc57-b4ce-41c0-b5c8-0b5a4d3d1cf3
-- title:
--   Corollary 13.10: for a convex β-smooth nonnegative loss and λ ≥ 2β/m, E_S[L_D(A(S))] ≤ (1 + 48β/(λm)) E_S[L_S(A(S))] ≤ (1 + 48β/(λm))(L_D(w*) + λ‖w*‖²)
-- statement:
--   **Corollary 13.10.** Assume that the loss function is convex, $\beta$-smooth, and nonnegative. Then the RLM rule with the regularization function $\lambda\|w\|^2$, for $\lambda \ge \frac{2\beta}{m}$, satisfies the following for all $w^*$:
--   $$\mathbb{E}_S[L_D(A(S))] \le \Big(1 + \frac{48\beta}{\lambda m}\Big)\mathbb{E}_S[L_S(A(S))] \le \Big(1 + \frac{48\beta}{\lambda m}\Big)\big(L_D(w^*) + \lambda\|w^*\|^2\big).$$
--    Measurability: jointly measurable loss and measurable algorithm, with a nonnegative loss bounded at the origin so that all expectations exist (for the RLM rule the minimizer is unique, so measurability of the algorithm is automatic).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §13.4 p. 180, Corollary 13.10 (from (13.16) and Corollary 13.7)

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 13.10** (p. 180). Assume that the loss function is convex, `β`-smooth and
nonnegative. Then the RLM rule with the regularization function `λ‖w‖²`, for `λ ≥ 2β/m`,
satisfies for all `w*`:
`E_S[L_D(A(S))] ≤ (1 + 48β/(λm)) E_S[L_S(A(S))] ≤ (1 + 48β/(λm))(L_D(w*) + λ‖w*‖²)`.
Measurability as in Corollary 13.6. -/
theorem rlm_smooth_oracle {d : ℕ} {Z : Type*} [MeasurableSpace Z] (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) (hnonneg : ∀ w z, 0 ≤ loss w z)
    {β : ℝ} (hβ : 0 ≤ β) (hsmooth : IsSmoothLoss β loss) {lam : ℝ} (hlam : 0 < lam)
    (A : Learner Z (Vec d)) (hA : IsRLMLearner loss lam A)
    (hmeas : Measurable (Function.uncurry loss)) {C : ℝ} (hC : ∀ z, loss 0 z ≤ C)
    (hAmeas : ∀ m, Measurable (A m)) (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ)
    (hm : 0 < m) (hlm : 2 * β / m ≤ lam) :
    ∫ S, risk loss D (A m S) ∂(iidLaw D m) ≤
      (1 + 48 * β / (lam * m)) * ∫ S, empRisk loss S (A m S) ∂(iidLaw D m) ∧
    ∀ wstar : Vec d, (1 + 48 * β / (lam * m)) * ∫ S, empRisk loss S (A m S) ∂(iidLaw D m) ≤
      (1 + 48 * β / (lam * m)) * (risk loss D wstar + lam * ‖wstar‖ ^ 2) := by sorry

end UnderstandingML
