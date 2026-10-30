-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_spectralNormLowerBound
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.spectralNormLowerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:23:25.594277+00:00
-- url     : https://prove2.me/theorems/0a633e55-cad5-42fb-a4b0-41020a706cfa
-- title:
--   §4: necessary spectral-norm lower bound on subnormalisation
-- statement:
--   Let $A$ be a real square matrix on a nonempty binary register, and let a unitary $U$ exactly block encode it with positive subnormalization $\alpha$, with the auxiliary register initialized and selected in a distinguished zero basis state. Then
--   $$ \|A\|_{\rm op}\le\alpha. $$
--   The norm is the L2 spectral/operator norm, and the exact block-encoding convention is $\alpha(\langle0|\otimes I)U(|0\rangle\otimes I)=A$. This necessary condition rules out proposed normalizations below the matrix norm, including some of the deferred examples.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 21, §4: necessary spectral-norm lower bound on subnormalisation

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF p.21, §4: a positive exact subnormalization bounds the spectral norm.
This uses the frozen auxiliary-first block-encoding and L2 operator norm. -/
theorem spectralNormLowerBound {F : Type*} [Fintype F] [DecidableEq F]
    (z : F) (U : Matrix (F × Fin (2 ^ n)) (F × Fin (2 ^ n)) ℂ)
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) (alpha : ℝ) (ha : 0 < alpha)
    (hU : QAlgorithms.IsBlockEncoding z U alpha 0 (complexMatrix A)) :
    QAlgorithms.specNorm (complexMatrix A) ≤ alpha := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
