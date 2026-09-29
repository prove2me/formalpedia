-- Prove2me | Theorems.Thm_RobustSDP_Uniqueness_feasible_tau_pos
-- name    : RobustSDP.Uniqueness.feasible_tau_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:05:54.062164+00:00
-- url     : https://prove2.me/theorems/7027c29c-c994-46a6-9c5e-eb6140f3e778
-- title:
--   §4.2 — Under H3(a) every feasible τ of (15) is positive; in particular τ_opt > 0
-- statement:
--   Consider the SDP (15), whose feasible points are the pairs $(x,\tau) \in \mathbb{R}^m \times \mathbb{R}$ with
--   $$\begin{bmatrix} F(x) - \tau L L^T & R(x)^T \\ R(x) & \tau I \end{bmatrix} \succeq 0 .$$
--   Under hypothesis H3(a), every feasible $(x,\tau)$ has
--   $$\tau > 0 .$$
--   In particular $\tau_{\mathrm{opt}} > 0$ at every optimal point $(x_{\mathrm{opt}}, \tau_{\mathrm{opt}})$.
--
--   Positivity of $\tau$ is what allows the Schur complement reformulation (16) of (15), on which the second-order analysis of §4.3 rests.
--
--   **Formalization Note** The statement is for every feasible point, as in the paper's "any $\tau$ that is feasible for (15) is nonzero"; nonnegativity of $\tau$ comes from the block $\tau I$.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 39, §4.2, first paragraph

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- §4.2, p. 39: under H3(a), every `τ` feasible for (15) is nonzero, hence positive; in
particular `τ_opt > 0`. -/
theorem feasible_tau_pos {m n p q : ℕ} (D : SDPData m n p q) (h3a : D.H3a)
    (y : (Fin m → ℝ) × ℝ) (hy : D.Feasible y) :
    0 < y.2 := by sorry

end RobustSDP.Uniqueness
