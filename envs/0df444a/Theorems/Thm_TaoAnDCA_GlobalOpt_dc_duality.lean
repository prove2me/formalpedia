-- Prove2me | Theorems.Thm_TaoAnDCA_GlobalOpt_dc_duality
-- name    : TaoAnDCA.GlobalOpt.dc_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:46.555466+00:00
-- url     : https://prove2.me/theorems/5ab46e65-9a34-4289-bfc0-166d86f528a8
-- title:
--   §3, (D), pp. 481–482 — d.c. duality: inf{g(x) − h(x)} = inf{h*(y) − g*(y)}
-- statement:
--   Let $g,h\in\Gamma_0(\mathbb R^n)$ satisfy the standing inclusions $\operatorname{dom}g\subset\operatorname{dom}h$ and $\operatorname{dom}h^*\subset\operatorname{dom}g^*$, and adopt the convention $+\infty-(+\infty)=+\infty$. Then the d.c. program (P) and its dual (D) have the same optimal value:
--   $$\alpha=\inf_{x\in X}\{g(x)-h(x)\}=\inf_{y\in Y}\{h^*(y)-g^*(y)\}.$$
--
--   This is the d.c. duality of §3 (Toland duality). The paper derives it by writing $h=h^{**}$, exchanging the two infima, and observing that $\inf_x\{g(x)-\langle x,y\rangle+h^*(y)\}=h^*(y)-g^*(y)$ for $y\in\operatorname{dom}h^*$ and $+\infty$ otherwise. It is the first step of the proof of the global optimality condition, Theorem 3.1(i).
--
--   **Formalization Note** Both sides are extended-real infima; the differences are the convention-respecting difference `dcSub`, so the dual objective is $+\infty$ off $\operatorname{dom}h^*$, as in the paper's rewriting of (D) over all of $Y$. No finiteness of $\alpha$ is assumed. The standing assumptions $g,h\in\Gamma_0$ and (3) are hypotheses.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), pp. 481–482, §3, derivation of (P_y) and display (D)

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open TaoAnDCA.GlobalOpt

namespace TaoAnDCA.GlobalOpt

theorem dc_duality {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : DCStanding g h) :
    primalValue g h =
      ⨅ y, dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y := by sorry

end TaoAnDCA.GlobalOpt
