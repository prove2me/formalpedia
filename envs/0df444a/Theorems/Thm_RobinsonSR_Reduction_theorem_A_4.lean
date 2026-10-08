-- Prove2me | Theorems.Thm_RobinsonSR_Reduction_theorem_A_4
-- name    : RobinsonSR.Reduction.theorem_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:10:56.340332+00:00
-- url     : https://prove2.me/theorems/98addd8a-133c-4650-899e-e45629184a64
-- title:
--   Theorem A.4, p. 60 — 0 ∈ Ax + a + ∂ψ_C(x), C polyhedral, is strongly regular at x₀ iff its reduced form is vacuous or uniquely solvable on all of L
-- statement:
--   Let $C$ be a nonempty polyhedral convex set in $\mathbb R^n$, let $A$ be a real $n\times n$ matrix and $a\in\mathbb R^n$, and suppose $x_0\in\mathbb R^n$ solves
--   $$0\in Ax+a+\partial\psi_C(x).\qquad\text{(A.1)}$$
--   Put $y_0:=Ax_0+a$, let $F:=\partial\psi_C^*(-y_0)$ be the face of $C$ on which $\langle -y_0,\cdot\rangle$ is maximal (it contains $x_0$), let $T:=T_F(x_0)$ be the tangent cone to $F$ at $x_0$, $L$ the subspace parallel to $F$, and $P_L$ the orthogonal projector on $L$. The reduced form of (A.1) at $x_0$ is the inclusion
--   $$z\in P_LAw+\partial\psi_T(w),\qquad z\in L.$$
--   Then (A.1) is strongly regular at $x_0$ (for some Lipschitz constant $\lambda$) if and only if its reduced form
--
--   1. is vacuous, that is, $L=\{0\}$; or
--   2. has an inverse which is single-valued on all of $L$: for every $z\in L$ there is exactly one $w\in\mathbb R^n$ with $z\in P_LAw+\partial\psi_T(w)$.
--
--   This is the paper's general criterion for strong regularity of a linear generalized equation over a polyhedral set: it reduces the question to unique solvability of a homogeneous problem on a cone, which Theorem 3.1 then settles for $\mathbb R^r\times K$ in terms of a Schur complement (Corollary 3.2).
--
--   **Formalization Note** The paper writes the reduced form in an orthonormal basis $b_1,\dots,b_n$ adapted to $M$ (the lineality space of $T$), $L\cap M^\perp$ and $L^\perp$, as $z\in Bw+\partial\psi_{\mathbb R^r\times K}(w)$ (A.3, A.5); the statement here is the coordinate-free form (A.4) on $L$ itself. Since $T\subseteq L$, every solution $w$ lies in $T\subseteq L$, and $\partial\psi_T(w)\supseteq L^\perp$, so the $L^\perp$ component of the inclusion is automatic. Disjunct (i) is a special case of (ii) (for $L=\{0\}$ the unique solution is $w=0$); both are kept as printed. "Strongly regular" without a constant is $\exists\lambda$. Nonemptiness of $C$ is the appendix's standing assumption and is implied by $x_0\in C$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 60, Theorem A.4 (with the construction of pp. 59–60 and (A.4))

import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- Theorem A.4 (Robinson 1980, p. 60). Let `C` be a (nonempty) polyhedral convex set in `ℝⁿ`,
`A` an `n × n` matrix and `a ∈ ℝⁿ`, and let `x₀` solve `0 ∈ A x + a + ∂ψ_C(x)` (A.1). With
`y₀ := A x₀ + a`, `F := ∂ψ*_C(-y₀)`, `T := T_F(x₀)` and `L` the subspace parallel to `F`,
(A.1) is strongly regular at `x₀` if and only if its reduced form (i) is vacuous (`L = {0}`), or
(ii) has an inverse which is single-valued on all of `L`: for every `z ∈ L` there is exactly one
`w` with `z ∈ P_L A w + ∂ψ_T(w)`. -/
theorem theorem_A_4 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n))
    (hsol : -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0) :
    let y0 := Matrix.toEuclideanLin A x0 + a
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    (∃ lam : ℝ, StronglyRegularLin C A a x0 lam) ↔
      (L = ⊥ ∨ ∀ z ∈ L, ∃! w : EuclideanSpace ℝ (Fin n),
        z - L.starProjection (Matrix.toEuclideanLin A w) ∈ normalCone T w) := by sorry

end RobinsonSR.Reduction
