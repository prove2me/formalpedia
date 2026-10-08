-- Prove2me | Theorems.Thm_SuttonBartoRL_Traces_lambda_return_recursion
-- name    : SuttonBartoRL.Traces.lambda_return_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:37:28.723985+00:00
-- url     : https://prove2.me/theorems/488f4ed2-7900-40f6-b841-8004f20844e0
-- title:
--   Exercise 12.1: $G^\lambda_t = R_{t+1} + \gamma[(1-\lambda)\hat v(S_{t+1},w) + \lambda G^\lambda_{t+1}]$
-- statement:
--   Let an episode of length $T$ with rewards $R_1, \dots, R_T$ and states $S_0, \dots, S_{T-1}$, a value function $\hat v$ with $\hat v(\text{terminal}, \cdot) = 0$ and a fixed weight vector $w$ be given; let $\gamma \in [0,1]$ and $\lambda \in [0, 1)$. Then the $\lambda$-return (12.2) satisfies, for every $t < T$,
--   $$
--   G^\lambda_t = R_{t+1} + \gamma\bigl[(1 - \lambda)\,\hat v(S_{t+1}, w) + \lambda\, G^\lambda_{t+1}\bigr].
--   $$
--   At $t = T - 1$ the right side is $R_T$, since the terminal value and $G^\lambda_T$ are both $0$.
--
--   This is the analogue for the $\lambda$-return of the recursion $G_t = R_{t+1} + \gamma G_{t+1}$ (3.9) for the return. Exercise 12.3 builds on it.
--
--   **Formalization Note** The book gives no solution; the displayed recursion is the answer it asks for, derived from (12.1) and (12.2). The weights are one fixed $w$ throughout, as in Exercise 12.3.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 12.1, p. 290 (no solution given in the book)

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_LambdaReturn

namespace SuttonBartoRL.Traces

/-- Sutton & Barto, Exercise 12.1, p. 290 (the book gives no solution): for a fixed weight vector
`w`, `λ ∈ [0, 1)` and `t < T`, `G^λ_t = R_{t+1} + γ [(1 − λ) v̂(S_{t+1}, w) + λ G^λ_{t+1}]`. -/
theorem lambda_return_recursion {St : Type} {d : ℕ} (γ lam : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) (ht : t < e.T) :
    lambdaReturn γ lam vhat w e t =
      e.R (t + 1) + γ * ((1 - lam) * value vhat w e (t + 1)
        + lam * lambdaReturn γ lam vhat w e (t + 1)) := by sorry

end SuttonBartoRL.Traces
