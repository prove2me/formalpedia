-- Prove2me | Theorems.Thm_SuttonBartoRL_Traces_offline_td_lambda_sum_equivalence
-- name    : SuttonBartoRL.Traces.offline_td_lambda_sum_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:37:39.363992+00:00
-- url     : https://prove2.me/theorems/2c608bb8-fe45-466e-aa5f-d07ac05fbe10
-- title:
--   Exercise 12.4: for fixed $w$, summed TD($\lambda$) updates equal summed off-line $\lambda$-return updates
-- statement:
--   Let an episode of length $T$ with states $S_0, \dots, S_{T-1}$ and rewards $R_1, \dots, R_T$ be given, together with a differentiable value function $\hat v(s, \cdot) : \mathbb R^d \to \mathbb R$ (with $\hat v(\text{terminal}, \cdot) = 0$), a step size $\alpha > 0$, $\gamma \in [0, 1]$, $\lambda \in [0, 1)$ and a weight vector $w$ that **remains fixed** over the episode. Let $\delta_t$ be the TD errors (12.6), $z_t$ the accumulating eligibility trace (12.5), $z_{-1} = 0$, $z_t = \gamma\lambda z_{t-1} + \nabla\hat v(S_t, w)$, and $G^\lambda_t$ the $\lambda$-return (12.2), all at $w$. Then
--   $$
--   \sum_{t=0}^{T-1} \alpha\, \delta_t\, z_t = \sum_{t=0}^{T-1} \alpha\,\bigl[G^\lambda_t - \hat v(S_t, w)\bigr]\,\nabla \hat v(S_t, w).
--   $$
--   The left side is the sum of TD($\lambda$)'s weight updates (12.7) and the right side is the sum of the off-line $\lambda$-return algorithm's updates (12.4).
--
--   This is the classical equivalence of the backward view (TD($\lambda$)) and the forward view (the $\lambda$-return algorithm) when the weights are not changed during the episode.
--
--   **Formalization Note** The book gives no solution. The fixed weight vector is one binder `w`; with changing weights the claim is false in general. $\nabla\hat v(s, w)$ is Mathlib's `gradient` on `EuclideanSpace ℝ (Fin d)`, and differentiability of each $\hat v(s, \cdot)$ is assumed as in the box on p. 293.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 12.4, p. 295 (no solution given in the book), with Eqs. (12.4)–(12.7), pp. 290–293

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_LambdaReturn

namespace SuttonBartoRL.Traces

/-- Sutton & Barto, Exercise 12.4, p. 295 (the book gives no solution): if the weight vector `w`
stays fixed over an episode, the sum over `t = 0, …, T−1` of TD(λ)'s updates `α δ_t z_t` ((12.5)–(12.7))
equals the sum of the off-line λ-return algorithm's updates `α [G^λ_t − v̂(S_t, w)] ∇v̂(S_t, w)` (12.4). -/
theorem offline_td_lambda_sum_equivalence {St : Type} {d : ℕ} (α γ lam : ℝ) (hα : 0 < α)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (hvhat : ∀ s, Differentiable ℝ (vhat s))
    (w : EuclideanSpace ℝ (Fin d)) (e : Episode St) :
    ∑ t ∈ Finset.range e.T, (α * tdError γ vhat w e t) • accTrace γ lam vhat w e t =
      ∑ t ∈ Finset.range e.T,
        (α * (lambdaReturn γ lam vhat w e t - value vhat w e t)) • gradient (vhat (e.S t)) w := by sorry

end SuttonBartoRL.Traces
