-- Prove2me | Theorems.Thm_RobustSDP_Uniqueness_h3a_R_ne_zero
-- name    : RobustSDP.Uniqueness.h3a_R_ne_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:05:30.493931+00:00
-- url     : https://prove2.me/theorems/5e226a73-099f-46ae-89df-e1851b1e2964
-- title:
--   §4.1 — Hypothesis H3(a) implies R(x) ≠ 0 for every x
-- statement:
--   Let $R(x) = R_0 + \sum_{i=1}^m x_i R_i$ with $R_i \in \mathbb{R}^{q\times n}$, and assume hypothesis H3(a): the nullspace of $\lambda R_0 + \sum_i x_i R_i$ is one and the same proper subspace $N \subsetneq \mathbb{R}^n$ for every $(\lambda, x) \neq (0,0)$. Then
--   $$R(x) \neq 0 \qquad \text{for every } x \in \mathbb{R}^m .$$
--
--   This is the remark by which the paper excludes $\tau = 0$ from the feasible set of (15), the first step towards the nonlinear reformulation (16).
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 38, §4.1, paragraph after H3

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- El Ghaoui–Oustry–Lebret (1998), §4.1, p. 38: "H3(a) implies that R(x) ≠ 0 for every x." -/
theorem h3a_R_ne_zero {m n p q : ℕ} (D : SDPData m n p q) (h3a : D.H3a) (x : Fin m → ℝ) :
    D.R x ≠ 0 := by sorry

end RobustSDP.Uniqueness
