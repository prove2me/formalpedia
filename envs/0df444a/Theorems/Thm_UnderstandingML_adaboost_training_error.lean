-- Prove2me | Theorems.Thm_UnderstandingML_adaboost_training_error
-- name    : UnderstandingML.adaboost_training_error
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:59:46.001316+00:00
-- url     : https://prove2.me/theorems/26512cb7-d632-4259-87f5-8cd6a12acb99
-- title:
--   Theorem 10.2: if every round of AdaBoost has εₜ ≤ 1/2 − γ, the training error of its output is at most exp(−2γ²T)
-- statement:
--   **Theorem 10.2.** Let $S$ be a training set and assume that at each iteration of AdaBoost, the weak learner returns a hypothesis for which $\epsilon_t \le 1/2 - \gamma$. Then the training error of the output hypothesis of AdaBoost is at most
--   $$L_S(h_s) = \frac1m \sum_{i=1}^m \mathbb{1}[h_s(x_i) \ne y_i] \le \exp(-2\gamma^2 T).$$
--
--   Formally: for $\gamma > 0$ and weak hypotheses with $0 < \epsilon_t \le 1/2 - \gamma$ in every round (the weight $w_t = \frac12 \log(1/\epsilon_t - 1)$ is undefined at $\epsilon_t = 0$), the empirical 0–1 risk of `adaBoost S h T` is at most $\exp(-2\gamma^2 T)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §10.2 pp. 135-137, Theorem 10.2 with its proof

import Definitions.Def_UnderstandingML_Boosting

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 10.2** (p. 135). Let `S` be a training set and assume that at each iteration of
AdaBoost the weak learner returns a hypothesis for which `εₜ ≤ 1/2 − γ`. Then the training error
of the output hypothesis of AdaBoost is at most
`L_S(h_s) = (1/m) ∑ᵢ 𝟙[h_s(xᵢ) ≠ yᵢ] ≤ exp(−2γ²T)`.
Stated with `γ > 0` and `εₜ > 0` (the weight `wₜ = ½ log(1/εₜ − 1)` is undefined at `εₜ = 0`). -/
theorem adaboost_training_error {X : Type*} {m : ℕ} (S : Fin m → X × Bool) (h : ℕ → X → Bool)
    (T : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hε : ∀ t < T, 0 < adaError S h t ∧ adaError S h t ≤ 1 / 2 - γ) :
    empRisk loss01 S (adaBoost S h T) ≤ Real.exp (-(2 * γ ^ 2 * T)) := by sorry

end UnderstandingML
