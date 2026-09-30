-- Prove2me | Theorems.Thm_UnderstandingML_rlm_oracle_inequality
-- name    : UnderstandingML.rlm_oracle_inequality
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:17:32.337982+00:00
-- url     : https://prove2.me/theorems/a5c63af6-1220-4027-9534-458d58f94b7c
-- title:
--   Corollary 13.8 (oracle inequality): for a convex ρ-Lipschitz loss, RLM satisfies E_S[L_D(A(S))] ≤ L_D(w*) + λ‖w*‖² + 2ρ²/(λm) for every w*
-- statement:
--   **Corollary 13.8.** Assume that the loss function is convex and $\rho$-Lipschitz. Then the RLM rule with the regularization function $\lambda\|w\|^2$ satisfies
--   $$\forall w^*,\quad \mathbb{E}_S[L_D(A(S))] \le L_D(w^*) + \lambda\|w^*\|^2 + \frac{2\rho^2}{\lambda m}.$$
--    Measurability: jointly measurable loss and measurable algorithm, with a nonnegative loss bounded at the origin so that all expectations exist (for the RLM rule the minimizer is unique, so measurability of the algorithm is automatic).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §13.4 p. 179, Corollary 13.8 with its derivation (13.15)-(13.16)

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 13.8** (p. 179). Assume that the loss function is convex and `ρ`-Lipschitz. Then
the RLM rule with the regularization function `λ‖w‖²` satisfies, for all `w*`,
`E_S[L_D(A(S))] ≤ L_D(w*) + λ‖w*‖² + 2ρ²/(λm)`. Measurability as in Corollary 13.6. -/
theorem rlm_oracle_inequality {d : ℕ} {Z : Type*} [MeasurableSpace Z] (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) {ρ : ℝ}
    (hlip : IsLipschitzLoss ρ loss) {lam : ℝ} (hlam : 0 < lam) (A : Learner Z (Vec d))
    (hA : IsRLMLearner loss lam A) (hmeas : Measurable (Function.uncurry loss))
    (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ} (hC : ∀ z, loss 0 z ≤ C)
    (hAmeas : ∀ m, Measurable (A m)) (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ)
    (hm : 0 < m) (wstar : Vec d) :
    ∫ S, risk loss D (A m S) ∂(iidLaw D m) ≤
      risk loss D wstar + lam * ‖wstar‖ ^ 2 + 2 * ρ ^ 2 / (lam * m) := by sorry

end UnderstandingML
