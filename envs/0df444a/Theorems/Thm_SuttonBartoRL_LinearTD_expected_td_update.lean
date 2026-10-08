-- Prove2me | Theorems.Thm_SuttonBartoRL_LinearTD_expected_td_update
-- name    : SuttonBartoRL.LinearTD.expected_td_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:47:39.451985+00:00
-- url     : https://prove2.me/theorems/5579642b-2932-4509-b4cf-a0b4c190a345
-- title:
--   Expected update of linear TD(0), $\mathbb E[\mathbf w_{t+1}\mid\mathbf w_t] = (\mathbf I - \alpha\mathbf A)\mathbf w_t + \alpha\mathbf b$ (9.13)
-- statement:
--   Let a finite MDP with dynamics $p(s', r \mid s, a)$, a policy $\pi$, a state distribution $\mu$ with $\sum_s \mu(s) = 1$, a feature matrix $\mathbf X$ with rows $\mathbf x(s) \in \mathbb R^d$, a discount rate $\gamma$ and a step size $\alpha$ be given, and let $\mathbf A$ and $\mathbf b$ be the matrix and vector of (9.11). Fix a weight vector $\mathbf w$ and draw $S_t \sim \mu$, $A_t \sim \pi(\cdot \mid S_t)$ and $(S_{t+1}, R_{t+1}) \sim p(\cdot, \cdot \mid S_t, A_t)$. Then the expected result of one linear semi-gradient TD(0) update (9.9) is
--
--   $$\mathbb E[\mathbf w_{t+1} \mid \mathbf w_t = \mathbf w] = \sum_s \mu(s) \sum_a \pi(a \mid s) \sum_{s', r} p(s', r \mid s, a)\Big[\mathbf w + \alpha\big(r + \gamma \mathbf w^\top \mathbf x(s') - \mathbf w^\top \mathbf x(s)\big)\mathbf x(s)\Big] = (\mathbf I - \alpha \mathbf A)\mathbf w + \alpha \mathbf b .$$
--
--   This is (9.13), the rewriting of (9.10) with which the book's convergence box starts: only $\mathbf A$ multiplies the weight vector, so the behaviour of the expected iteration is governed by $\mathbf A$.
--
--   **Formalization Note** The expectation is written as the finite sum over the steady-state distribution of one transition, as the book's "once the system has reached steady state" (p. 205) intends. The identity only needs $\mu$ to sum to one; that $\mu$ is the stationary distribution matters for the later items, not for this one.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (9.9)–(9.10), p. 205; Eq. (9.13), box "Proof of Convergence of Linear TD(0)", p. 206

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

namespace SuttonBartoRL.LinearTD

/-- Sutton & Barto (2018), (9.10) and (9.13), pp. 205–206: in steady state (`S_t ∼ µ`,
`A_t ∼ π(·|S_t)`, `(S_{t+1}, R_{t+1}) ∼ p(·, ·|S_t, A_t)`), the expected linear semi-gradient TD(0)
update (9.9) from a fixed weight vector `w` is `E[w_{t+1} | w_t = w] = (I − αA)w + αb`, with `A`, `b`
of (9.11). -/
theorem expected_td_update {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) (γ α : ℝ)
    (hμsum : ∑ s, μ s = 1) (w : Fin d → ℝ) :
    ∑ s, μ s • ∑ a, π.prob s a • ∑ s', ∑ r ∈ M.R, M.p s a s' r • tdUpdate X γ α w s r s' =
      (1 - α • tdA M π μ X γ) *ᵥ w + α • tdB M π μ X := by sorry

end SuttonBartoRL.LinearTD
