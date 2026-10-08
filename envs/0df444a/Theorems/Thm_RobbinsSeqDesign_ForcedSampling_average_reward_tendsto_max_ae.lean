-- Prove2me | Theorems.Thm_RobbinsSeqDesign_ForcedSampling_average_reward_tendsto_max_ae
-- name    : RobbinsSeqDesign.ForcedSampling.average_reward_tendsto_max_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:11.173077+00:00
-- url     : https://prove2.me/theorems/8eb25058-5358-4932-838f-423c56f8864d
-- title:
--   Section 2, Eq. (14) — under $\bar R$, $S_n/n \to \max(\alpha,\beta)$ with probability 1
-- statement:
--   Let $A$ and $B$ be two populations whose expectations $\alpha$ and $\beta$ exist (are finite), let $1 = a_1 < a_2 < \cdots$ and $2 = b_1 < b_2 < \cdots$ be disjoint sequences of density $0$, and sample according to Robbins' rule $\bar R$: forced draws from $A$ at the times $a_j$ and from $B$ at the times $b_j$, and otherwise a draw from the population whose running mean is larger (ties to $B$). With $S_n = x_1 + \cdots + x_n$, with probability 1,
--   $$\lim_{n\to\infty} \frac{S_n}{n} = \max(\alpha, \beta).$$
--
--   This is the almost-sure form of the statement that $\bar R$ asymptotically does as well, per draw, as an experimenter who knows which population is better. The paper attributes it to the strong law of large numbers.
--
--   **Formalization Note.** "The expectations exist" is the hypothesis that both reward laws are integrable; no further condition (variance, boundedness) is assumed, and $\alpha=\beta$ is allowed. "With probability 1" is an almost-everywhere statement under the trajectory law `banditTrajMeasure ν (rule σ)`.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 532, Section 2, Eq. (14)

import Mathlib
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Rule
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Loss

namespace RobbinsSeqDesign.ForcedSampling

open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm

/-- Robbins (1952), Section 2, Eq. (14), p. 532: for any two populations A, B whose
expectations `α`, `β` exist (are finite) and any pair of sequences (13), under the rule `R̄`,
with probability 1, `S_n / n → max(α, β)`. -/
theorem average_reward_tendsto_max_ae (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    ∀ᵐ ω ∂(banditTrajMeasure ν (rule σ)),
      Tendsto (fun n : ℕ => partialSum n ω / (n : ℝ)) atTop
        (𝓝 (max (banditArmMean ν 0) (banditArmMean ν 1))) := by sorry

end RobbinsSeqDesign.ForcedSampling
