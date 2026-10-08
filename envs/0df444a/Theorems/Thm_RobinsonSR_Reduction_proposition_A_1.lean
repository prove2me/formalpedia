-- Prove2me | Theorems.Thm_RobinsonSR_Reduction_proposition_A_1
-- name    : RobinsonSR.Reduction.proposition_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:00.787299+00:00
-- url     : https://prove2.me/theorems/cf44ce6b-bd3f-4f68-8be2-52ba72526908
-- title:
--   Proposition A.1, p. 58 — for polyhedral C and x₀ ∈ C, (C − x₀) ∩ U = T_C(x₀) ∩ U near the origin
-- statement:
--   Let $C$ be a nonempty polyhedral convex set in $\mathbb R^n$ and let $x_0\in C$. Write $T_C(x_0)=\partial\psi_C(x_0)^\circ$ for the tangent cone to $C$ at $x_0$, the polar of the normal cone. Then there exists a neighbourhood $U$ of the origin such that
--   $$(C-x_0)\cap U=T_C(x_0)\cap U.$$
--
--   Near $x_0$ a polyhedral set coincides with its tangent cone translated to $x_0$. This is the first of the three properties of polyhedral convex sets that the paper's reduction of a linear generalized equation to reduced form rests on.
--
--   **Formalization Note** $C-x_0$ is the image of $C$ under $c\mapsto c-x_0$. The standing assumption of the appendix ("$C$ is a nonempty polyhedral convex set in $\mathbb R^n$", p. 58) is carried as hypotheses; nonemptiness is implied by $x_0\in C$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 58, Proposition A.1

import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- Proposition A.1 (Robinson 1980, p. 58). Let `C` be a nonempty polyhedral convex set in `ℝⁿ`
and `x₀ ∈ C`. Then there is a neighbourhood `U` of the origin with
`(C - x₀) ∩ U = T_C(x₀) ∩ U`, where `T_C(x₀) = ∂ψ_C(x₀)°`. -/
theorem proposition_A_1 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ C) :
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ((fun c => c - x0) '' C) ∩ U = tangentCone C x0 ∩ U := by sorry

end RobinsonSR.Reduction
