-- Prove2me | Theorems.Thm_ParamSDO_Transition_semialgebraic_frontier_finite
-- name    : ParamSDO.Transition.semialgebraic_frontier_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:14.85498+00:00
-- url     : https://prove2.me/theorems/379aca0f-e7d6-47db-a92e-15b57b564527
-- title:
--   [5, Theorem 5.22], cited p. 22 — a semi-algebraic subset of ℝ has only finitely many boundary points
-- statement:
--   Let $T\subseteq\mathbb R$ be semi-algebraic, i.e. a finite union of sets $\{x\in\mathbb R:\ p_1(x)=\dots=p_k(x)=0,\ g_1(x)<0,\dots,g_l(x)<0\}$ with real polynomials $p_i,g_j$. Then its topological boundary is finite:
--   $$
--   \#\operatorname{bd}(T)<\infty .
--   $$
--
--   The paper cites this fact from Basu, Pollack and Roy, *Algorithms in Real Algebraic Geometry*, Theorem 5.22, to conclude Theorem 1.
--
--   **Formalization Note** A subset of $\mathbb R$ is encoded as a subset of $\mathbb R^1$ (`Fin 1 → ℝ`). This statement involves no SDO data, so it carries no standing assumptions.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 22, Appendix, proof of Theorem 1, citing [5] Basu–Pollack–Roy, Algorithms in Real Algebraic Geometry, Theorem 5.22

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem semialgebraic_frontier_finite :
    ∀ T : Set ℝ, IsSemialgebraicReal T → (frontier T).Finite := by sorry

end ParamSDO.Transition
