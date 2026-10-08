-- Prove2me | Theorems.Thm_RobbinsSeqDesign_ForcedSampling_forced_sampling_loss_tendsto_zero
-- name    : RobbinsSeqDesign.ForcedSampling.forced_sampling_loss_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:30.870111+00:00
-- url     : https://prove2.me/theorems/2b7de957-7bc5-4667-8b1d-fa0a81ad3785
-- title:
--   Section 2, Eq. (16) — the loss of $\bar R$ tends to 0 for any two populations with finite means
-- statement:
--   Let $A$ and $B$ be any two populations whose expectations $\alpha$ and $\beta$ exist (are finite), and let
--   $$1 = a_1 < a_2 < \cdots, \qquad 2 = b_1 < b_2 < \cdots$$
--   be disjoint sequences of positive integers of density $0$. Then Robbins' rule $\bar R$ (forced draws from $A$ at the $a$'s and from $B$ at the $b$'s, otherwise from the population with the larger running mean, ties to $B$) satisfies
--   $$\lim_{n\to\infty} L_n(A, B, \bar R) = \max(\alpha,\beta) - \lim_{n\to\infty} E\!\left(\frac{S_n}{n}\right) = 0,$$
--   where $L_n(A,B,R) = \max(\alpha,\beta) - E(S_n/n)$ is the loss of display (9).
--
--   This answers affirmatively Robbins' question (12) — whether some rule $R$ has $\lim_n L_n(A,B,R) = 0$ for every $A, B$ — not only for coins but for any two populations with finite means, and it does so with one explicit rule, uniformly in the choice of the density-zero schedule. In later terminology: a forced-exploration greedy policy has regret $o(n)$ on every two-armed bandit with integrable rewards.
--
--   **Formalization Note.** "For any $A, B$ such that $\alpha, \beta$ exist" is: for every two-armed `StochasticBandit` with both reward laws integrable; no other restriction on the class of populations is imposed, and $\alpha=\beta$ is allowed. The statement is for the specific rule $\bar R$ and every admissible schedule, not merely the existence of some rule. The limit is along $n \to \infty$ in $\mathbb N$.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 532, Section 2, Eq. (16) (answering (12))

import Mathlib
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Rule
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Loss

namespace RobbinsSeqDesign.ForcedSampling

open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm

/-- Robbins (1952), Section 2, Eq. (16), p. 532: for any two populations A, B such that
`α`, `β` exist (are finite) and any pair of sequences (13), the loss (9) of the rule `R̄`
tends to zero: `lim_{n→∞} L_n(A, B, R̄) = 0`. -/
theorem forced_sampling_loss_tendsto_zero (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    Tendsto (fun n : ℕ => loss ν (rule σ) n) atTop (𝓝 0) := by sorry

end RobbinsSeqDesign.ForcedSampling
