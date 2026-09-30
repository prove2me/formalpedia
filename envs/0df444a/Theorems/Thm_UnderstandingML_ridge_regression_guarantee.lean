-- Prove2me | Theorems.Thm_UnderstandingML_ridge_regression_guarantee
-- name    : UnderstandingML.ridge_regression_guarantee
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:19:19.31629+00:00
-- url     : https://prove2.me/theorems/eca6343e-b268-47f0-b768-346bb9a553f1
-- title:
--   Theorem 13.1: for D over the unit ball × [−1,1] and H the ball of radius B, ridge regression with λ = ε/(3B²) and m ≥ 150B²/ε² has E_S[L_D(A(S))] ≤ min_{w∈H} L_D(w) + ε
-- statement:
--   **Theorem 13.1.** Let $D$ be a distribution over $X \times [-1,1]$, where $X = \{x \in \mathbb{R}^d : \|x\| \le 1\}$. Let $H = \{w \in \mathbb{R}^d : \|w\| \le B\}$. For any $\epsilon \in (0,1)$, let $m \ge 150 B^2/\epsilon^2$. Then applying the ridge regression algorithm with parameter $\lambda = \epsilon/(3B^2)$ satisfies $\mathbb{E}_{S \sim D^m}[L_D(A(S))] \le \min_{w \in H} L_D(w) + \epsilon$, for the loss $\frac12(\langle w,x\rangle - y)^2$ of (13.3).
--
--   Formally: the support condition on $D$ is almost sure; the ridge algorithm is any RLM learner for this loss (its output is unique). The loss is $1$-smooth on the support, since $\|x\| \le 1$, and $\ell(0, z) = y^2/2 \le 1/2$; the constant $150$ holds for the reason given at Corollary 13.11.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §13.1.1 p. 173, Theorem 13.1 (from Corollary 13.11); sample-size constant corrected from 150 to 216

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 13.1** (p. 173). Let
`D` be a distribution over `X × [−1, 1]`, where `X = {x ∈ ℝ^d : ‖x‖ ≤ 1}`, and let
`H = {w ∈ ℝ^d : ‖w‖ ≤ B}`. For any `ε ∈ (0, 1)`, let `m ≥ 150 B²/ε²`.
Then applying the ridge regression algorithm with parameter `λ = ε/(3B²)` satisfies
`E_{S ∼ D^m}[L_D(A(S))] ≤ min_{w ∈ H} L_D(w) + ε`, for the loss `½(⟨w, x⟩ − y)²` of (13.3). The
support condition is stated almost surely; the ridge algorithm is any RLM learner for this loss
(its output is unique and measurable). -/
theorem ridge_regression_guarantee {d : ℕ} (D : Measure (Vec d × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, ‖z.1‖ ≤ 1 ∧ |z.2| ≤ 1) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (m : ℕ) (hm : 150 * B ^ 2 / ε ^ 2 ≤ m) (A : Learner (Vec d × ℝ) (Vec d))
    (hA : IsRLMLearner ridgeLoss (ε / (3 * B ^ 2)) A) (hAmeas : ∀ m, Measurable (A m)) :
    ∀ w : Vec d, ‖w‖ ≤ B →
      ∫ S, risk ridgeLoss D (A m S) ∂(iidLaw D m) ≤ risk ridgeLoss D w + ε := by sorry

end UnderstandingML
