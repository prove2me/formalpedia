-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_jensen_block_calculus
-- name    : TroppMatrixConcentration.ch8_jensen_block_calculus
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:47:33.127763+00:00
-- url     : https://prove2.me/theorems/e7d23d5f-9762-40b3-8864-200906edbe1a
-- title:
--   Functional calculus and spectrum of a block-diagonal Hermitian matrix
-- statement:
--   Let $A$ and $B$ be finite-dimensional Hermitian matrices over $\mathbb C$, and let $f:\mathbb R\to\mathbb R$ be any function. Their block sum is Hermitian and satisfies
--   $$\operatorname{spec}_{\mathbb R}(A\oplus B)=\operatorname{spec}_{\mathbb R}(A)\cup\operatorname{spec}_{\mathbb R}(B),\qquad f(A\oplus B)=f(A)\oplus f(B).$$
--   No global continuity assumption is needed because these spectra are finite.
-- source:
--   Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, proof of Theorem 8.5.2, printed pp. 132–133 (PDF pp. 138–139), block-diagonal functional-calculus identities.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_jensen_block_calculus
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.fromBlocks A 0 0 B).IsHermitian ∧
    spectrum ℝ (Matrix.fromBlocks A 0 0 B) = spectrum ℝ A ∪ spectrum ℝ B ∧
    ch8_matrixFunction f (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (ch8_matrixFunction f A) 0 0 (ch8_matrixFunction f B) := by sorry

end TroppMatrixConcentration
