-- Prove2me | Theorems.Thm_UnderstandingML_adaboost_reweighted_error
-- name    : UnderstandingML.adaboost_reweighted_error
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:00:30.664177+00:00
-- url     : https://prove2.me/theorems/e471be6c-da71-4cb0-80cf-fec813dc0662
-- title:
--   Exercise 10.3: the error of hₜ with respect to the updated distribution D⁽ᵗ⁺¹⁾ is exactly 1/2
-- statement:
--   **Exercise 10.3.** The AdaBoost weighting mechanism forces the weak learner to focus on the problematic examples: the error of $h_t$ with respect to the distribution $D^{(t+1)}$ is exactly $1/2$, that is, for every $t \in [T]$, $\sum_{i=1}^m D^{(t+1)}_i \mathbb{1}[y_i \ne h_t(x_i)] = 1/2$.
--
--   Formally: for a nonempty sample and $\epsilon_t \in (0,1)$, the weighted error of $h_t$ under `adaDist S h (t+1)` equals $1/2$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §10.7 Exercise 10.3 pp. 142-143

import Definitions.Def_UnderstandingML_Boosting

open MeasureTheory

namespace UnderstandingML

/-- **Exercise 10.3** (p. 143). The error of `hₜ` with respect to the updated distribution
`D⁽ᵗ⁺¹⁾` is exactly `1/2`: `∑ᵢ Dᵢ⁽ᵗ⁺¹⁾ 𝟙[yᵢ ≠ hₜ(xᵢ)] = 1/2`. Stated for a nonempty sample and
`εₜ ∈ (0, 1)`, where the weight `wₜ` is defined. -/
theorem adaboost_reweighted_error {X : Type*} {m : ℕ} (hm : 0 < m) (S : Fin m → X × Bool)
    (h : ℕ → X → Bool) (t : ℕ) (hε : 0 < adaError S h t ∧ adaError S h t < 1) :
    weightedError (adaDist S h (t + 1)) S (h t) = 1 / 2 := by sorry

end UnderstandingML
