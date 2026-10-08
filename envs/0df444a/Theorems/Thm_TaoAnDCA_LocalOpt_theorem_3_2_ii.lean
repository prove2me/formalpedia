-- Prove2me | Theorems.Thm_TaoAnDCA_LocalOpt_theorem_3_2_ii
-- name    : TaoAnDCA.LocalOpt.theorem_3_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:58.267162+00:00
-- url     : https://prove2.me/theorems/f73c7156-358c-45a2-a07f-fd1a07fd025c
-- title:
--   Theorem 3.2(ii), p. 484 — a dual sufficient condition: h*(y) − g*(y) ≥ h*(y*) − g*(y*) for some y ∈ ∂h(x) makes x* a local minimizer
-- statement:
--   Let $g, h \in \Gamma_0(\mathbb R^n)$ satisfy the standing inclusions $\operatorname{dom} g \subset \operatorname{dom} h$ and $\operatorname{dom} h^* \subset \operatorname{dom} g^*$, with differences taken under the convention $+\infty - (+\infty) = +\infty$. Let $x^*$ be a critical point of $g - h$ and let
--   $$y^* \in \partial g(x^*) \cap \partial h(x^*).$$
--   Let $U$ be a neighbourhood of $x^*$ such that $U \cap \operatorname{dom} g \subset \operatorname{dom} \partial h$. Suppose that for every $x \in U \cap \operatorname{dom} g$ there is $y \in \partial h(x)$ with
--   $$h^*(y) - g^*(y) \ge h^*(y^*) - g^*(y^*).$$
--   Then $x^*$ is a local minimizer of $g - h$. More precisely,
--   $$g(x) - h(x) \ge g(x^*) - h(x^*) \qquad \forall x \in U \cap \operatorname{dom} g.$$
--
--   The authors call this condition new: it certifies local optimality in the primal program through values of the dual objective $h^* - g^*$. Applied to the dual pair $(h^*, g^*)$ it is the core of Corollary 3.5.
--
--   **Formalization Note.** "$x^*$ is a critical point and $y^* \in \partial g(x^*) \cap \partial h(x^*)$" is the single hypothesis on $y^*$, which already implies criticality. $\operatorname{dom}\partial h$ is the set of points where $\partial h$ is nonempty. Both dual values are the convention-respecting difference `dcSub (conj h) (conj g)`, and the conclusion contains both the local-minimizer claim and its "more precisely" form.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 484, Theorem 3.2(ii)

import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- Theorem 3.2 (ii), p. 484: let `x*` be a critical point of `g − h` and
`y* ∈ ∂g(x*) ∩ ∂h(x*)`, and let `U` be a neighbourhood of `x*` with `U ∩ dom g ⊂ dom ∂h`.
If for every `x ∈ U ∩ dom g` there is `y ∈ ∂h(x)` with `h*(y) − g*(y) ≥ h*(y*) − g*(y*)`,
then `x*` is a local minimizer of `g − h`; more precisely
`g(x) − h(x) ≥ g(x*) − h(x*)` for all `x ∈ U ∩ dom g`. -/
theorem theorem_3_2_ii {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (xs ys : EuclideanSpace ℝ (Fin n)) (hys : ys ∈ TaoAnDCA.GlobalOpt.subdiff g xs ∩ TaoAnDCA.GlobalOpt.subdiff h xs)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ 𝓝 xs)
    (hdom : U ∩ TaoAnDCA.GlobalOpt.effDom g ⊆ {x | (TaoAnDCA.GlobalOpt.subdiff h x).Nonempty})
    (hcond : ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, ∃ y ∈ TaoAnDCA.GlobalOpt.subdiff h x,
      TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys ≤
        TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y) :
    IsDCLocalMin g h xs ∧ ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, TaoAnDCA.GlobalOpt.dcSub g h xs ≤ TaoAnDCA.GlobalOpt.dcSub g h x := by sorry

end TaoAnDCA.LocalOpt
