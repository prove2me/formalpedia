-- Prove2me | Theorems.Thm_TaoAnDCA_LocalOpt_theorem_3_2_i
-- name    : TaoAnDCA.LocalOpt.theorem_3_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:54.895275+00:00
-- url     : https://prove2.me/theorems/8ea4a924-f82f-400b-aa07-fd42feaed0fb
-- title:
--   Theorem 3.2(i), p. 484 — a local minimizer x* of g − h satisfies ∂h(x*) ⊂ ∂g(x*)
-- statement:
--   Let $g, h \in \Gamma_0(\mathbb R^n)$ satisfy the standing inclusions $\operatorname{dom} g \subset \operatorname{dom} h$ and $\operatorname{dom} h^* \subset \operatorname{dom} g^*$, and let the d.c. difference $g - h$ be taken with the convention $+\infty - (+\infty) = +\infty$. If $x^*$ is a local minimizer of $g - h$ (that is, $g(x^*) - h(x^*)$ is finite and $g(x^*) - h(x^*) \le g(x) - h(x)$ for all $x$ in a neighbourhood of $x^*$), then $x^* \in \mathcal P_l$:
--   $$\partial h(x^*) \subset \partial g(x^*).$$
--
--   This is the classical necessary condition for local optimality in d.c. programming; it is the first step in transporting a local minimizer of the primal program to the dual one (Corollary 3.5).
--
--   **Formalization Note.** Local minimizer and $\mathcal P_l$ are the definitions of `TaoAnDCA.LocalOpt.Setting`; the standing assumptions are the structure `DCStanding g h`.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 484, Theorem 3.2(i)

import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- Theorem 3.2 (i), p. 484: a local minimizer `x*` of `g − h` lies in `𝒫_l`,
i.e. `∂h(x*) ⊂ ∂g(x*)`. -/
theorem theorem_3_2_i {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (xs : EuclideanSpace ℝ (Fin n)) (hloc : IsDCLocalMin g h xs) :
    xs ∈ Pl g h := by sorry

end TaoAnDCA.LocalOpt
