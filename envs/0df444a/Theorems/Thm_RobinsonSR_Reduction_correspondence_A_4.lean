-- Prove2me | Theorems.Thm_RobinsonSR_Reduction_correspondence_A_4
-- name    : RobinsonSR.Reduction.correspondence_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:10:37.928295+00:00
-- url     : https://prove2.me/theorems/8bd2e192-b58a-4f3a-8ed2-38a8784b822b
-- title:
--   (A.4), p. 60 — for x near x₀ and small y, y ∈ Ax + a + ∂ψ_C(x) iff 0 ∈ P_L(Ah − y) + ∂ψ_T(h), h = x − x₀
-- statement:
--   Let $C$ be a nonempty polyhedral convex set in $\mathbb R^n$, $A$ a real $n\times n$ matrix and $a\in\mathbb R^n$, and suppose $x_0$ solves the linear generalized equation
--   $$0\in Ax+a+\partial\psi_C(x).\qquad\text{(A.1)}$$
--   Put $y_0:=Ax_0+a$, $F:=\partial\psi_C^*(-y_0)$, $T:=T_F(x_0)$, and let $L$ be the subspace parallel to $F$ and $P_L$ the orthogonal projector on $L$. Then there are neighbourhoods $N$ of $x_0$ and $W$ of $0$ such that for every $x\in N$ and $y\in W$, with $h:=x-x_0$,
--   $$y\in Ax+a+\partial\psi_C(x)\ \text{(A.2)}\quad\Longleftrightarrow\quad 0\in P_L(Ah-y)+\partial\psi_T(h).\ \text{(A.4)}$$
--
--   This is the correspondence between solutions of the perturbed linear generalized equation (A.2) near $x_0$ and solutions of the reduced problem on the cone $T$; written in an orthonormal basis adapted to $L$ and to the lineality space of $T$, (A.4) becomes the reduced form $z\in Bw+\partial\psi_{\mathbb R^r\times K}(w)$ (A.3).
--
--   **Formalization Note** (A.2) is written as $y-(Ax+a)\in\partial\psi_C(x)$ and (A.4), equivalently, as $P_Ly-P_L(Ah)\in\partial\psi_T(h)$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 60, construction preceding Theorem A.4, (A.2) and (A.4)

import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- The correspondence (A.4) (Robinson 1980, p. 60). Let `C` be a nonempty polyhedral convex set
in `ℝⁿ`, `A` an `n × n` matrix, `a ∈ ℝⁿ`, and let `x₀` solve `0 ∈ A x + a + ∂ψ_C(x)` (A.1).
With `y₀ := A x₀ + a`, `F := ∂ψ*_C(-y₀)`, `T := T_F(x₀)` and `L` the subspace parallel to `F`,
there are neighbourhoods `N` of `x₀` and `W` of `0` such that for `x ∈ N` and `y ∈ W`,
`y ∈ A x + a + ∂ψ_C(x)` (A.2) holds if and only if `0 ∈ P_L(A h - y) + ∂ψ_T(h)` with
`h := x - x₀` (A.4), written here as `P_L y - P_L (A h) ∈ ∂ψ_T(h)`. -/
theorem correspondence_A_4 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n))
    (hsol : -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0) :
    let y0 := Matrix.toEuclideanLin A x0 + a
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    ∃ N ∈ 𝓝 x0, ∃ W ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∀ x ∈ N, ∀ y ∈ W,
      (y - (Matrix.toEuclideanLin A x + a) ∈ normalCone C x ↔
        L.starProjection y - L.starProjection (Matrix.toEuclideanLin A (x - x0)) ∈
          normalCone T (x - x0)) := by sorry

end RobinsonSR.Reduction
