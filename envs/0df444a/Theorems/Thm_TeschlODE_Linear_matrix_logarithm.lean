-- Prove2me | Theorems.Thm_TeschlODE_Linear_matrix_logarithm
-- name    : TeschlODE.Linear.matrix_logarithm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:57:02.32333+00:00
-- url     : https://prove2.me/theorems/07009f0c-3b32-4928-a95f-06cb5f4dfff0
-- title:
--   Lemma 3.34 — a matrix has a logarithm iff det ≠ 0; real logarithms
-- statement:
--   A **logarithm** of a square matrix $A$ is a matrix $B$ with $\exp(B) = A$ (3.200). Lemma 3.34 makes three claims:
--
--   1. A (complex) matrix $A \in \mathbb{C}^{n\times n}$ has a logarithm if and only if $\det A \neq 0$.
--   2. If $A \in \mathbb{R}^{n\times n}$ and every real eigenvalue of $A$ is positive, then $A$ has a real logarithm $B \in \mathbb{R}^{n\times n}$.
--   3. If $A \in \mathbb{R}^{n\times n}$ (with $\det A \ne 0$), then $A^2$ has a real logarithm.
--   $$\exists B:\ e^{B} = A \iff \det A \neq 0.$$
--
--   Claim 1 is what turns the monodromy matrix of a periodic system into $\exp(TQ)$ in Floquet's theorem; claims 2–3 give the real version, Corollary 3.16.
--
--   **Formalization Note.** $\exp$ is Mathlib's `NormedSpace.exp` on `Matrix (Fin n) (Fin n) 𝕂`. "Real eigenvalue $\mu$ of $A$" is `Module.End.HasEigenvalue (Matrix.toLin' A) μ` for $\mu \in \mathbb{R}$, which for a real matrix is the same as $\mu$ being a real root of its characteristic polynomial. In claim 3 the hypothesis $\det A \neq 0$ is added: the book states claim 3 inside the paragraph that begins "Hence suppose that $\det(A) \neq 0$" (p. 108), and without it the claim is false ($A = 0$, where $A^2 = 0$ has no logarithm).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 108, Lemma 3.34

import Mathlib

namespace TeschlODE.Linear

/-- Teschl, Lemma 3.34 (p. 108), all three claims. A logarithm of `A` is a matrix `B` with
`exp(B) = A` (3.200). (1) A complex matrix has a logarithm iff `det A ≠ 0`. (2) A real matrix
all of whose real eigenvalues are positive has a real logarithm. (3) For a real matrix `A`
(with `det A ≠ 0`, the standing assumption of the paragraph (3.200)–(3.202)), `A²` has a real
logarithm. -/
theorem matrix_logarithm (n : ℕ) :
    (∀ A : Matrix (Fin n) (Fin n) ℂ,
      (∃ B : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp B = A) ↔ A.det ≠ 0) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → 0 < μ) →
      ∃ B : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp B = A) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A.det ≠ 0 →
      ∃ B : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp B = A * A) := by sorry

end TeschlODE.Linear
