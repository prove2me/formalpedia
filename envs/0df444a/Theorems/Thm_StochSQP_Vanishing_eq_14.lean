-- Prove2me | Theorems.Thm_StochSQP_Vanishing_eq_14
-- name    : StochSQP.Vanishing.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:04.857379+00:00
-- url     : https://prove2.me/theorems/37754390-a957-4f65-abac-2fb91245c491
-- title:
--   (14), §3, p. 7 — the merit parameter rule guarantees Δl ≥ τ_k u_kᵀH_ku_k + σ(‖c_k‖₂ − ‖c_k + J_kv_k‖₂)
-- statement:
--   Consider a run of the stochastic SQP algorithm (Algorithm 1) for $\min f(x)$ s.t. $c(x) = 0$, with valid parameters, under Assumption 1 on an open convex set $X$ containing all iterates and Assumption 3 on the matrices $H_k$. Write $c_k = c(x_k)$, $J_k = J(x_k)$, and $\Delta l(x,\tau,g,d) = -\tau g^T d + \|c(x)\|_2 - \|c(x) + J(x)d\|_2$ for the reduction in the linear model of the merit function. Then for every $k \in \mathbb N$,
--   $$\Delta l(x_k, \tau_k, g_k, d_k) \ \ge\ \tau_k u_k^T H_k u_k + \sigma\big(\|c_k\|_2 - \|c_k + J_k v_k\|_2\big).$$
--
--   This is the fact the authors single out as critical for the analysis: the merit parameter rule (11)–(12) makes the model reduction at least a fixed fraction of the decrease in linearized infeasibility produced by the normal step, plus the curvature of the tangential step.
--
--   **Formalization Note.** Pathwise statement over runs; see the definitions file for the run model and the dropped probabilistic clauses.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 7, §3, (14)

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem eq_14 {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH) :
    ∀ k : ℕ, R.τ k * ⟪R.u k, R.H k (R.u k)⟫_ℝ +
        A.σ * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) ≤
      deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by sorry

end StochSQP.Vanishing
