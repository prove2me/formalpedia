-- Prove2me | Theorems.Thm_PassivityUn_commJ_iff_blocks
-- name    : PassivityUn.commJ_iff_blocks
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T21:14:52.747976+00:00
-- url     : https://prove2.me/theorems/18076706-3eb1-44c2-affa-9f9341ff4160
-- title:
--   Commuting with $J$ forces the block form $\begin{pmatrix} A & -B \\ B & A \end{pmatrix}$
-- statement:
--   Let $n$ be a natural number, let $A, B, C, D$ be real $n\times n$ matrices, and let $J_n = \begin{pmatrix} 0 & -I_n \\ I_n & 0 \end{pmatrix}$. Then
--
--   $$
--   \begin{pmatrix} A & B \\ C & D \end{pmatrix} J_n = J_n \begin{pmatrix} A & B \\ C & D \end{pmatrix}
--   \quad\Longleftrightarrow\quad D = A \ \text{ and } \ B = -C.
--   $$
--
--   So a real $2n\times 2n$ matrix commutes with $J_n$ exactly when its top-left and bottom-right blocks agree and its top-right block is the negative of its bottom-left block, i.e. it is the real form of a complex $n\times n$ matrix.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(b) (block form): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityUn_stdJ

namespace PassivityUn
theorem commJ_iff_blocks (n : ℕ) (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.fromBlocks A B C D * stdJ n = stdJ n * Matrix.fromBlocks A B C D
      ↔ D = A ∧ B = -C := by sorry
end PassivityUn
