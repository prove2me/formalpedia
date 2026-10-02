-- Prove2me | Theorems.Thm_TeschlODE_SturmLiouville_symmetric_eigenvalues_real_orthogonal
-- name    : TeschlODE.SturmLiouville.symmetric_eigenvalues_real_orthogonal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T11:24:44.725519+00:00
-- url     : https://prove2.me/theorems/7c3ae733-b632-4321-b4da-6526bb7bf7b7
-- title:
--   Theorem 5.4 — eigenvalues of a symmetric operator are real, eigenvectors orthogonal
-- statement:
--   Let $H_0$ be a complex inner product space and $A : D(A) \to H_0$ a symmetric operator: $D(A)$ is dense and $\langle g, Af\rangle = \langle Ag, f\rangle$ for $f, g \in D(A)$. Then
--
--   1. every eigenvalue $z$ of $A$ is real: if $A u = z u$ for some nonzero $u \in D(A)$, then $\operatorname{Im} z = 0$;
--   2. eigenvectors for different eigenvalues are orthogonal: if $A u_1 = z_1 u_1$, $A u_2 = z_2 u_2$ with $u_1, u_2 \ne 0$ and $z_1 \ne z_2$, then
--   $$\langle u_1, u_2\rangle = 0 .$$
--
--   This is the first structural fact about the eigenvalue problem; applied to the Sturm–Liouville operator $L$ it shows that its eigenvalues are real and its eigenfunctions mutually orthogonal in $H_0$.
--
--   **Formalization Note.** $H_0$ is not assumed complete. Eigenvalues are taken in $\mathbb{C}$ and reality is stated as `z.im = 0`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 149, Theorem 5.4

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_IsSymmetricOp

namespace TeschlODE.SturmLiouville

/-- Teschl, Theorem 5.4, p. 149: let `A : D(A) → H₀` be symmetric (dense domain and (5.36)).
Then every eigenvalue of `A` is real, and eigenvectors corresponding to different eigenvalues
are orthogonal. `H₀` is a complex inner product space, not assumed complete. -/
theorem symmetric_eigenvalues_real_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (D : Submodule ℂ E) (A : D →ₗ[ℂ] E) (hA : IsSymmetricOp D A) :
    (∀ (z : ℂ) (u : D), u ≠ 0 → A u = z • (u : E) → z.im = 0) ∧
    (∀ (z₁ z₂ : ℂ) (u₁ u₂ : D), u₁ ≠ 0 → u₂ ≠ 0 → A u₁ = z₁ • (u₁ : E) →
      A u₂ = z₂ • (u₂ : E) → z₁ ≠ z₂ → inner ℂ (u₁ : E) (u₂ : E) = 0) := by sorry

end TeschlODE.SturmLiouville
