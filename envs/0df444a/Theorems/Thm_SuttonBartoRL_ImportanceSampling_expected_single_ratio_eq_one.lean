-- Prove2me | Theorems.Thm_SuttonBartoRL_ImportanceSampling_expected_single_ratio_eq_one
-- name    : SuttonBartoRL.ImportanceSampling.expected_single_ratio_eq_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:30:26.052241+00:00
-- url     : https://prove2.me/theorems/a2457d9f-bfb3-4b43-b94c-324a09ab3605
-- title:
--   Each factor $\pi(A_k|S_k)/b(A_k|S_k)$ has expectation one (5.13)
-- statement:
--   Let $b$ cover $\pi$. For any state $x$, if the action is drawn from the behaviour policy, $A \sim b(\cdot \mid x)$, then the single importance-sampling factor has expectation one:
--
--   $$
--   \sum_a b(a \mid x)\, \frac{\pi(a \mid x)}{b(a \mid x)} = \sum_a \pi(a \mid x) = 1 .
--   $$
--
--   This is the reason why the factors of $\rho_{t:T-1}$ that follow a reward have no effect on its expectation, which leads to per-decision importance sampling.
--
--   **Formalization Note** The sum runs over all actions; terms with $b(a \mid x) = 0$ are $0$ in Lean (real division by zero), and by coverage $\pi(a \mid x) = 0$ for those actions, so the sum agrees with the book's sum over the actions $b$ can take.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.9, Eq. (5.13), p. 114

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_MDP

namespace SuttonBartoRL.ImportanceSampling

/-- Sutton & Barto (2018), §5.9, p. 114, Eq. (5.13): under coverage, the expected value of a single
factor of the importance-sampling ratio, given the state `S_k = x` and `A_k ∼ b(·|x)`, is one:
`Σ_a b(a|x) · π(a|x)/b(a|x) = Σ_a π(a|x) = 1`. -/
theorem expected_single_ratio_eq_one {S A : Type} [Fintype A]
    (π b : SuttonBartoRL.FiniteMDP.Policy S A) (hcov : Coverage π b) (x : S) :
    ∑ a, b.prob x a * (π.prob x a / b.prob x a) = ∑ a, π.prob x a ∧
    ∑ a, π.prob x a = 1 := by sorry

end SuttonBartoRL.ImportanceSampling
