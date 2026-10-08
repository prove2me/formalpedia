-- Prove2me | Theorems.Thm_TaoAnDCA_LocalOpt_corollary_3_5
-- name    : TaoAnDCA.LocalOpt.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:00.978553+00:00
-- url     : https://prove2.me/theorems/3ef0b439-87ed-43d7-96a0-8eb470c52189
-- title:
--   Corollary 3.5, p. 485 — d.c. duality transports a local minimizer x* of g − h to a local minimizer y* ∈ ∂h(x*) of h* − g*
-- statement:
--   Let $g, h \in \Gamma_0(\mathbb R^n)$ satisfy the standing inclusions $\operatorname{dom} g \subset \operatorname{dom} h$ and $\operatorname{dom} h^* \subset \operatorname{dom} g^*$, with differences taken under the convention $+\infty - (+\infty) = +\infty$. Let $x^* \in \operatorname{dom} g$ admit an open neighbourhood $U$ such that
--   $$g(x) - h(x) \ge g(x^*) - h(x^*) \qquad \forall x \in U \cap \operatorname{dom} g,$$
--   so that $x^*$ is a local minimizer of $g - h$, and let $y^* \in \partial h(x^*)$. If
--   $$y^* \in \operatorname{int}(\operatorname{dom} g^*) \quad\text{and}\quad \partial g^*(y^*) \subset U, \tag{12}$$
--   then $y^*$ is a local minimizer of the dual d.c. objective $h^* - g^*$: the value $h^*(y^*) - g^*(y^*)$ is finite and
--   $$h^*(y^*) - g^*(y^*) \le h^*(y) - g^*(y) \qquad \text{for all } y \text{ in a neighbourhood of } y^*.$$
--
--   This is the duality transportation of local minimizers: a local solution of the primal d.c. program (P) produces a local solution of the dual program (D), which matters when (D) is easier to solve locally than (P). It improves Toland's earlier result, which assumed $g^*$ differentiable on the whole space.
--
--   **Formalization Note.** The neighbourhood $U$ of the local-minimum property is named because (12) refers to it, and it is taken open: the proof's upper-semicontinuity step needs an open set containing $\partial g^*(y^*)$. The page's "$x^* \in \operatorname{dom}\partial h$" follows from $y^* \in \partial h(x^*)$; $x^* \in \operatorname{dom} g$ is the finiteness part of "local minimizer". The conclusion is the full local-minimizer predicate (4) for the pair $(h^*, g^*)$, including finiteness.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 485, Corollary 3.5, (12)

import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- Corollary 3.5, p. 485 (d.c. duality transportation of a local minimizer): let `x*` be a
local minimizer of `g − h` with neighbourhood `U` (`g(x) − h(x) ≥ g(x*) − h(x*)` for all
`x ∈ U ∩ dom g`), and let `y* ∈ ∂h(x*)`. If `y* ∈ int (dom g*)` and `∂g*(y*) ⊂ U` (12), then
`y*` is a local minimizer of `h* − g*`. The neighbourhood `U` is taken open, as the proof's
upper-semicontinuity step requires. -/
theorem corollary_3_5 {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (xs ys : EuclideanSpace ℝ (Fin n)) (hfin : xs ∈ TaoAnDCA.GlobalOpt.effDom g)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hxU : xs ∈ U)
    (hmin : ∀ x ∈ U, x ∈ TaoAnDCA.GlobalOpt.effDom g → TaoAnDCA.GlobalOpt.dcSub g h xs ≤ TaoAnDCA.GlobalOpt.dcSub g h x)
    (hy : ys ∈ TaoAnDCA.GlobalOpt.subdiff h xs)
    (h12a : ys ∈ interior (TaoAnDCA.GlobalOpt.effDom (CondatPD.FinDim.conj g)))
    (h12b : TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) ys ⊆ U) :
    IsDCLocalMin (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys := by sorry

end TaoAnDCA.LocalOpt
