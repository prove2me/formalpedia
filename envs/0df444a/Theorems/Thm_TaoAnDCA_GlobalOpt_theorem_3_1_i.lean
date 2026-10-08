-- Prove2me | Theorems.Thm_TaoAnDCA_GlobalOpt_theorem_3_1_i
-- name    : TaoAnDCA.GlobalOpt.theorem_3_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:24.524922+00:00
-- url     : https://prove2.me/theorems/16d3b7d3-286d-45fa-aca3-569f641bad80
-- title:
--   Theorem 3.1(i), p. 483 — x ∈ dom h solves min(g − h) if and only if ∂_εh(x) ⊂ ∂_εg(x) for every ε > 0
-- statement:
--   Let $g,h:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be proper, lower semicontinuous and convex, and assume the inclusions
--   $$\operatorname{dom}g\subset\operatorname{dom}h,\qquad\operatorname{dom}h^*\subset\operatorname{dom}g^*,$$
--   where $h^*,g^*$ are the conjugate functions. Consider the d.c. program
--   $$\text{(P)}\qquad \alpha=\inf\{g(x)-h(x):x\in\mathbb R^n\}$$
--   with the convention $+\infty-(+\infty)=+\infty$, and let $\mathcal P$ be its set of solutions. For $\varepsilon>0$ let $\partial_\varepsilon\theta(x)$ denote the $\varepsilon$-subdifferential of a convex function $\theta$ at $x\in\operatorname{dom}\theta$.
--
--   Then for every $x\in\operatorname{dom}h$,
--   $$x\in\mathcal P\iff \partial_\varepsilon h(x)\subset\partial_\varepsilon g(x)\quad\forall\varepsilon>0.$$
--
--   This is the global optimality condition for d.c. programs, first established by Hiriart-Urruty; the paper gives a short proof through the d.c. duality. It characterizes global minimizers of a nonconvex objective by inclusions between convex objects.
--
--   **Formalization Note** The paper states (i) for every $x$; its proof argues for $x^*\in\operatorname{dom}h$. The statement is restricted to $x\in\operatorname{dom}h$ because for $x\notin\operatorname{dom}h$ the set $\partial_\varepsilon h(x)$ is empty, so the right-hand side holds vacuously while $x\notin\mathcal P$, and the unrestricted statement would be false. The restriction loses nothing: every solution lies in $\operatorname{dom}g\subset\operatorname{dom}h$, and for $x\in\operatorname{dom}h\setminus\operatorname{dom}g$ both sides are false. The $\varepsilon$-subdifferential is empty outside the domain, as in the paper's definition; the difference $g-h$ uses the convention $+\infty-(+\infty)=+\infty$ (`dcSub`). The standing assumptions ($g,h\in\Gamma_0$ and the inclusions (3), assumed throughout the paper) are hypotheses; finiteness of $\alpha$ is not assumed.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 483, Theorem 3.1(i)

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open TaoAnDCA.GlobalOpt

namespace TaoAnDCA.GlobalOpt

theorem theorem_3_1_i {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ effDom h) :
    x ∈ primalSol g h ↔ ∀ ε : ℝ, 0 < ε → epsSubdiff h ε x ⊆ epsSubdiff g ε x := by sorry

end TaoAnDCA.GlobalOpt
