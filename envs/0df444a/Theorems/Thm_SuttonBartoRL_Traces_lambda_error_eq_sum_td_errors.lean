-- Prove2me | Theorems.Thm_SuttonBartoRL_Traces_lambda_error_eq_sum_td_errors
-- name    : SuttonBartoRL.Traces.lambda_error_eq_sum_td_errors
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:37:27.761211+00:00
-- url     : https://prove2.me/theorems/f453cc6d-1b2d-4d0c-830b-14f97fb13a5a
-- title:
--   Exercise 12.3: for fixed $w$, $G^\lambda_t - \hat v(S_t,w) = \sum_{k=t}^{T-1} (\gamma\lambda)^{k-t}\delta_k$
-- statement:
--   Let an episode of length $T$, a value function $\hat v$ with $\hat v(\text{terminal}, \cdot) = 0$ and a **single fixed** weight vector $w$ be given; let $\gamma \in [0,1]$ and $\lambda \in [0, 1)$. Let $\delta_k = R_{k+1} + \gamma \hat v(S_{k+1}, w) - \hat v(S_k, w)$ be the TD errors (12.6). Then for every $t < T$ the error term of the off-line $\lambda$-return algorithm (12.4) is
--   $$
--   G^\lambda_t - \hat v(S_t, w) = \sum_{k=t}^{T-1} (\gamma\lambda)^{k-t}\, \delta_k .
--   $$
--
--   This is the $\lambda$-return analogue of (6.6), which writes the Monte Carlo error as a sum of TD errors. It explains why TD($\lambda$) approximates the off-line $\lambda$-return algorithm.
--
--   **Formalization Note** The book gives no solution. The weight vector is one binder `w` used in every term; with the algorithm's changing weights $w_t$ the identity is false in general.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 12.3, p. 295 (no solution given in the book), with Eqs. (12.4) and (12.6), pp. 290 and 293

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_LambdaReturn

namespace SuttonBartoRL.Traces

/-- Sutton & Barto, Exercise 12.3, p. 295 (the book gives no solution): for a single fixed weight
vector `w`, the error term of the off-line λ-return algorithm (12.4) is a discounted sum of TD errors
(12.6): `G^λ_t − v̂(S_t, w) = Σ_{k=t}^{T−1} (γλ)^{k−t} δ_k` for `t < T`. -/
theorem lambda_error_eq_sum_td_errors {St : Type} {d : ℕ} (γ lam : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) :
    lambdaReturn γ lam vhat w e t - value vhat w e t =
      ∑ k ∈ Finset.Ico t e.T, (γ * lam) ^ (k - t) * tdError γ vhat w e k := by sorry

end SuttonBartoRL.Traces
