-- Prove2me | Theorems.Thm_PassivityUn_admissible_finrank
-- name    : PassivityUn.admissible_finrank
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T21:17:09.166978+00:00
-- url     : https://prove2.me/theorems/c5407d55-1667-41ee-ab9d-f2e7c410860a
-- title:
--   Passivity-admissible couplings have dimension n² = dim u(n)
-- statement:
--   Let $n$ be a natural number, and consider real $2n\times 2n$ matrices in $2\times 2$ block form with $n\times n$ blocks. Let
--
--   $$
--   J_n = \begin{pmatrix} 0 & -I_n \\ I_n & 0 \end{pmatrix}.
--   $$
--
--   The set of real $2n\times 2n$ matrices $W$ that are
--
--   1. symmetric, $W^{\mathsf T} = W$, and
--   2. commute with $J_n$, $WJ_n = J_nW$,
--
--   is a real vector space $\mathcal{A}_n$ of dimension exactly $n^2$:
--
--   $$
--   \dim_{\mathbb{R}} \mathcal{A}_n = n^2 .
--   $$
--
--   This is the dimension of the unitary Lie algebra $\mathfrak{u}(n)$. At $n = 1, 2, 3$ it gives $1, 4, 9$, the dimensions of $\mathfrak{u}(1)$, $\mathfrak{u}(2) = \mathfrak{u}(1)\oplus\mathfrak{su}(2)$ and $\mathfrak{u}(3) = \mathfrak{u}(1)\oplus\mathfrak{su}(3)$. The statement is pure linear algebra; it does not assert the physical premise that passivity forces a coupling to be symmetric.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(b): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityUn_admissible

namespace PassivityUn
theorem admissible_finrank (n : ℕ) :
    Module.finrank ℝ (admissible n) = n ^ 2 := by sorry
end PassivityUn
