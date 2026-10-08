-- Prove2me | Theorems.Thm_SuttonBartoRL_Traces_lambda_return_finite_form
-- name    : SuttonBartoRL.Traces.lambda_return_finite_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:37:18.192259+00:00
-- url     : https://prove2.me/theorems/df55a4e2-ade8-4953-b95c-74703eef2918
-- title:
--   Eq. (12.3): the $\lambda$-return with its post-termination terms separated
-- statement:
--   Let an episode of length $T$ with rewards $R_1, \dots, R_T$, states $S_0, \dots, S_{T-1}$, a value function $\hat v$ and a fixed weight vector $w$ be given; let $\gamma \in [0, 1]$ and $\lambda \in [0, 1)$. Let $G_{t:t+n}$ be the $n$-step returns (12.1), $G_t$ the return, and $G^\lambda_t$ the $\lambda$-return (12.2). Then for every $t < T$ the series (12.2) converges and
--   $$
--   G^\lambda_t = (1 - \lambda) \sum_{n=1}^{T-t-1} \lambda^{n-1} G_{t:t+n} + \lambda^{T-t-1} G_t .
--   $$
--
--   Every $n$-step return with $t + n \ge T$ equals the full return, so the infinite tail of (12.2) collapses to a single term. This finite form shows what happens at the extremes: $\lambda = 0$ gives the one-step return $G_{t:t+1}$.
--
--   **Formalization Note** The conclusion includes summability of $n \mapsto \lambda^{n} G_{t:t+n+1}$, since (12.2) is a `tsum`. The sum is written with $n$ shifted down by one. $\lambda = 1$ is excluded because (12.2) is defined for $\lambda \in [0, 1)$ (p. 289). The value function and the weights play no role in the convergence.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (12.3), derived from Eq. (12.2), pp. 289–290

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_LambdaReturn

namespace SuttonBartoRL.Traces

/-- Sutton & Barto, (12.3) from (12.2), pp. 289–290: for `λ ∈ [0, 1)` and `t < T`, the series (12.2)
converges and `G^λ_t = (1 − λ) Σ_{n=1}^{T−t−1} λ^{n−1} G_{t:t+n} + λ^{T−t−1} G_t`
(the sum written with `n` shifted down by one). The weight vector `w` is fixed. -/
theorem lambda_return_finite_form {St : Type} {d : ℕ} (γ lam : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) :
    Summable (fun n : ℕ => lam ^ n * nstepReturn γ vhat w e t (n + 1)) ∧
      lambdaReturn γ lam vhat w e t =
        (1 - lam) * ∑ n ∈ Finset.range (e.T - t - 1), lam ^ n * nstepReturn γ vhat w e t (n + 1)
          + lam ^ (e.T - t - 1) * ret γ e t := by sorry

end SuttonBartoRL.Traces
