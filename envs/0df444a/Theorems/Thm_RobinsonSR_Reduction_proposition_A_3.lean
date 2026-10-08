-- Prove2me | Theorems.Thm_RobinsonSR_Reduction_proposition_A_3
-- name    : RobinsonSR.Reduction.proposition_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:31.985025+00:00
-- url     : https://prove2.me/theorems/09302300-f112-4371-a313-1d79d9b4ce75
-- title:
--   Proposition A.3, p. 58 — near 0, 0 ∈ (y₀ + k) + ∂ψ_C(x₀ + h) iff 0 ∈ P_L k + ∂ψ_T(h), T = T_F(x₀)
-- statement:
--   Let $C$ be a nonempty polyhedral convex set in $\mathbb R^n$, let $y_0\in\mathbb R^n$ and $F:=\partial\psi_C^*(-y_0)$, and let $x_0\in F$. Write $T:=T_F(x_0)$ for the tangent cone to $F$ at $x_0$, let $L$ be the subspace parallel to $F$, and let $P_L$ denote the orthogonal projector on $L$. Then there exist neighbourhoods $U$ and $V$ of the origin such that for each $h\in U$ and each $k\in V$,
--   $$0\in(y_0+k)+\partial\psi_C(x_0+h)\quad\Longleftrightarrow\quad 0\in P_Lk+\partial\psi_T(h).$$
--
--   This is the key step of the appendix: near a point of the face $F$, the perturbed inclusion on $C$ is equivalent to an inclusion on the cone $T$ in which only the component of the perturbation in $L$ matters. Applied with $y_0=Ax_0+a$ it yields the correspondence (A.4) between solutions of the linear generalized equation and of its reduced form.
--
--   **Formalization Note** The inclusions are written as $-(y_0+k)\in\partial\psi_C(x_0+h)$ and $-P_Lk\in\partial\psi_T(h)$. $\partial\psi_T$ is the normal cone of $T$ in all of $\mathbb R^n$ (it contains $L^\perp$), with the ∅ clause off $T$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 58, Proposition A.3

import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- Proposition A.3 (Robinson 1980, p. 58). Let `C` be a nonempty polyhedral convex set in `ℝⁿ`,
`y₀ ∈ ℝⁿ`, `F := ∂ψ*_C(-y₀)`, `x₀ ∈ F`, `T := T_F(x₀)` and `L` the subspace parallel to `F`.
Then there are neighbourhoods `U` and `V` of the origin such that for each `h ∈ U` and `k ∈ V`,
`0 ∈ (y₀ + k) + ∂ψ_C(x₀ + h)` if and only if `0 ∈ P_L k + ∂ψ_T(h)`, where `P_L` is the
orthogonal projector on `L`. -/
theorem proposition_A_3 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (y0 x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ exposedFace C y0) :
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∃ V ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ∀ h ∈ U, ∀ k ∈ V,
        (-(y0 + k) ∈ normalCone C (x0 + h) ↔ -(L.starProjection k) ∈ normalCone T h) := by sorry

end RobinsonSR.Reduction
