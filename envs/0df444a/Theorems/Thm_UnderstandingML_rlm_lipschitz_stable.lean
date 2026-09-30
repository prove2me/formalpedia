-- Prove2me | Theorems.Thm_UnderstandingML_rlm_lipschitz_stable
-- name    : UnderstandingML.rlm_lipschitz_stable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:16:45.077307+00:00
-- url     : https://prove2.me/theorems/99329c43-36b9-4965-9ea6-e5cdf2e98b57
-- title:
--   Corollary 13.6: for a convex ρ-Lipschitz loss, RLM with λ‖w‖² is on-average-replace-one-stable with rate 2ρ²/(λm), so E_S[L_D(A(S)) − L_S(A(S))] ≤ 2ρ²/(λm)
-- statement:
--   **Corollary 13.6.** Assume that the loss function is convex and $\rho$-Lipschitz. Then the RLM rule with the regularizer $\lambda\|w\|^2$ is on-average-replace-one-stable with rate $\frac{2\rho^2}{\lambda m}$. It follows (using Theorem 13.2) that $\mathbb{E}_{S \sim D^m}[L_D(A(S)) - L_S(A(S))] \le \frac{2\rho^2}{\lambda m}$.
--
--   Formally: the pointwise bound $\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i) \le 2\rho^2/(\lambda m)$ for every $S, z', i$ (the book's derivation), stability with that rate, and the expectation bound. Measurability: jointly measurable loss and measurable algorithm, with a nonnegative loss bounded at the origin so that all expectations exist (for the RLM rule the minimizer is unique, so measurability of the algorithm is automatic).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §13.3.1 pp. 176-177, Corollary 13.6 with its derivation (13.7)-(13.11)

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 13.6** (p. 177). Assume that the loss function is convex and `ρ`-Lipschitz. Then
the RLM rule with the regularizer `λ‖w‖²` is on-average-replace-one-stable with rate
`2ρ²/(λm)`; it follows (using Theorem 13.2) that `E_{S ∼ D^m}[L_D(A(S)) − L_S(A(S))] ≤ 2ρ²/(λm)`.
The first clause is the book's pointwise bound `ℓ(A(S⁽ⁱ⁾), zᵢ) − ℓ(A(S), zᵢ) ≤ 2ρ²/(λm)`, which
holds for every `S, z', i`. The expectation clause assumes a nonnegative, jointly measurable loss
bounded at the origin and a measurable RLM learner (automatic: the minimizer is unique). -/
theorem rlm_lipschitz_stable {d : ℕ} {Z : Type*} [MeasurableSpace Z] (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) {ρ : ℝ}
    (hlip : IsLipschitzLoss ρ loss) {lam : ℝ} (hlam : 0 < lam) (A : Learner Z (Vec d))
    (hA : IsRLMLearner loss lam A) (hmeas : Measurable (Function.uncurry loss))
    (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ} (hC : ∀ z, loss 0 z ≤ C)
    (hAmeas : ∀ m, Measurable (A m)) :
    (∀ (m : ℕ), 0 < m → ∀ (S : Fin m → Z) (i : Fin m) (z' : Z),
        loss (A m (Function.update S i z')) (S i) - loss (A m S) (S i) ≤ 2 * ρ ^ 2 / (lam * m)) ∧
    OnAverageReplaceOneStable loss A (fun m ↦ 2 * ρ ^ 2 / (lam * m)) ∧
    ∀ (D : Measure Z), IsProbabilityMeasure D → ∀ m : ℕ, 0 < m →
      ∫ S, (risk loss D (A m S) - empRisk loss S (A m S)) ∂(iidLaw D m) ≤
        2 * ρ ^ 2 / (lam * m) := by sorry

end UnderstandingML
