-- Prove2me | Theorems.Thm_UnderstandingML_bernoulli_mle_hoeffding
-- name    : UnderstandingML.bernoulli_mle_hoeffding
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:32:57.652053+00:00
-- url     : https://prove2.me/theorems/f5086ddd-4d5d-4fc6-a1b7-c4ded32cc815
-- title:
--   Equation (24.2): for a Bernoulli(θ) sample of size m, |θ̂ − θ| ≤ √(log(2/δ)/(2m)) with probability at least 1 − δ
-- statement:
--   **Equation (24.2).** Since $\hat\theta$ is the average of $m$ i.i.d. binary random variables we can use Hoeffding's inequality to get that with probability of at least $1-\delta$ over the choice of $S$ we have that $|\hat\theta - \theta| \le \sqrt{\log(2/\delta)/(2m)}$.
--
--   Formally: $m \ge 1$, $\theta \in [0,1]$, $\delta \in (0,1)$, the failure event $\{|\hat\theta - \theta| > \sqrt{\log(2/\delta)/(2m)}\}$ has probability at most $\delta$ under the i.i.d. Bernoulli law.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §24.1 p. 343, Equation (24.2) (Hoeffding's inequality)

import Definitions.Def_UnderstandingML_Generative

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Equation (24.2)** (p. 343). Since `θ̂` is the average of `m` i.i.d. binary random variables,
by Hoeffding's inequality, with probability of at least `1 − δ` over the choice of `S` we have
`|θ̂ − θ| ≤ √(log(2/δ)/(2m))`. `m ≥ 1`, `δ ∈ (0, 1)`, `θ ∈ [0, 1]`. -/
theorem bernoulli_mle_hoeffding (m : ℕ) (hm : 0 < m) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw (bernoulliLaw θ) m {S | Real.sqrt (Real.log (2 / δ) / (2 * m)) < |bernoulliMLE S - θ|} ≤
      ENNReal.ofReal δ := by sorry

end UnderstandingML
