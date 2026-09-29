-- Prove2me | Theorems.Thm_PassivityUn_symm_blocks_iff
-- name    : PassivityUn.symm_blocks_iff
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T21:16:00.713465+00:00
-- url     : https://prove2.me/theorems/f2b82f08-11b2-4ef3-9667-99c0b6fb66ff
-- title:
--   Symmetric block form $\iff$ $A$ symmetric, $B$ antisymmetric
-- statement:
--   Let $n$ be a natural number and let $A, B$ be real $n\times n$ matrices. Then
--
--   $$
--   \begin{pmatrix} A & -B \\ B & A \end{pmatrix}^{\mathsf T} = \begin{pmatrix} A & -B \\ B & A \end{pmatrix}
--   \quad\Longleftrightarrow\quad A^{\mathsf T} = A \ \text{ and } \ B^{\mathsf T} = -B.
--   $$
--
--   In complex terms, the real form of $A + iB$ is symmetric exactly when $A + iB$ is Hermitian.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(b) (block form): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib

open Matrix

namespace PassivityUn
theorem symm_blocks_iff (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.fromBlocks A (-B) B A)ᵀ = Matrix.fromBlocks A (-B) B A
      ↔ Aᵀ = A ∧ Bᵀ = -B := by sorry
end PassivityUn
