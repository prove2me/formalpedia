-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_figureOfMerit
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.figureOfMerit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:09:12.964217+00:00
-- url     : https://prove2.me/theorems/8624ff21-72b5-43df-960f-53f616aa33d3
-- title:
--   §2.1.2: figure-of-merit comparison (18)
-- statement:
--   Let $A$ be a real $N\times N$ matrix, with $N>0$, $D\le N$ supplied data items, and column and row sparsity bounds $S_c,S_r\le N$. Write $\|A\|_F$ for its Frobenius norm and $\|A\|_{\max}$ for its largest entry magnitude. Then
--   $$ (N^2+N)\|A\|_F\ge N^2\|A\|_{\max}\ge D\sqrt{S_cS_r}\,\|A\|_{\max}. $$
--   This compares the product of table-loading count and subnormalization for the base scheme with the quantum-data-structure reference. It is a non-strict inequality and also applies to the zero matrix.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 8, §2.1.2: figure-of-merit comparison (18)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF p.8, (18): the real target is used with the accepted Frobenius norm. -/
theorem figureOfMerit (N D Sc Sr : ℕ) (hN : 0 < N) (hD : D ≤ N)
    (hc : Sc ≤ N) (hr : Sr ≤ N) (A : Matrix (Fin N) (Fin N) ℝ) :
    (((N : ℝ) ^ 2 + N) * QAlgorithms.frobNorm (complexMatrix A) ≥
      (N : ℝ) ^ 2 * matrixMax A) ∧
    ((N : ℝ) ^ 2 * matrixMax A ≥
      D * Real.sqrt ((Sc : ℝ) * Sr) * matrixMax A) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
