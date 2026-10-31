-- Prove2me | Theorems.Thm_RobustToDynamics_step1_lyapunov_solution
-- name    : RobustToDynamics.step1_lyapunov_solution
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:09.755007+00:00
-- url     : https://prove2.me/theorems/0e0b93ea-8fd9-4d2c-bba0-76ef77e5659f
-- title:
--   Step 1, (2.14) — for $\rho(G)<1$ the Lyapunov equation $G^TMG-M=-I$ has a unique solution, and it is positive definite
-- statement:
--   Let $G$ be a real $n\times n$ matrix with spectral radius $\rho(G)<1$. Then the Lyapunov equation
--   $$
--   G^TMG-M=-I \tag{2.14}
--   $$
--   has exactly one solution $M\in\mathbb R^{n\times n}$, and this solution is symmetric positive definite, $M\succ0$.
--
--   The matrix $M$ defines the ellipsoids $E(\alpha)=\{x: x^TMx\le\alpha\}$ that are invariant under $x\mapsto Gx$, the first step of the proof of Theorem 2.7.
--
--   **Formalization Note** Uniqueness is among all real $n\times n$ matrices. Positive definiteness (`Matrix.PosDef`) includes symmetry.
--
--   Differences from the source:
--   - generalization: rational data → real data; reason: the statement for real matrices specializes to rational ones by casting
--   - generalization: unique solution, for the symmetric matrix M → unique among all real n × n matrices; reason: stronger than uniqueness among symmetric matrices, and the unique solution is symmetric
--   - encoding: ρ(G) = max of |λ| over the (real or complex) eigenvalues → specRadius, the supremum of |z| over the complex spectrum; reason: the complex spectrum of an n × n matrix is finite and nonempty for n ≥ 1, so the supremum is the maximum; same value
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 1, display (2.14), p.14

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius

open Matrix

namespace RobustToDynamics

/-- **Step 1, (2.14): the Lyapunov equation has a unique solution, and it is positive definite.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 1, display (2.14), p.14: "we solve the well-known Lyapunov equation GT MG − M = −I, for the
symmetric matrix M … Since ρ(G) < 1, this linear system is guaranteed to have a unique solution
… Further, we claim that M must be positive definite."

If the real `n × n` matrix `G` has spectral radius `ρ(G) < 1`, there is a matrix `M` with
`GᵀMG − M = −I` that is positive definite (in particular symmetric), and every real matrix solving
`GᵀMG − M = −I` equals it.

**Formalization Note.** `ρ(G)` is `specRadius` (complex spectrum). Uniqueness is among all real
`n × n` matrices, not only symmetric ones (a generalization: the paper's unique symmetric solution
is a special case). `Matrix.PosDef` includes symmetry (`IsHermitian` over `ℝ`). Real `G`
generalizes the paper's rational `G`. -/
theorem step1_lyapunov_solution {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : specRadius G < 1) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, (Gᵀ * M * G - M = -1 ∧ M.PosDef) ∧
      ∀ M' : Matrix (Fin n) (Fin n) ℝ, Gᵀ * M' * G - M' = -1 → M' = M := by sorry

end RobustToDynamics
