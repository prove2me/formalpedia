-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_bell_transpose_identity
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.bell_transpose_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:31:42.567147+00:00
-- url     : https://prove2.me/theorems/f8d9ee59-1b55-4a44-a3c8-442d815d3c67
-- title:
--   Transpose transfer on the unnormalized Bell vector
-- statement:
--   Let $d\ge2$, use the same fixed computational orthonormal basis on both factors, and let $X$ be any complex $d\times d$ matrix. Write $|\widetilde\psi^+\rangle=\sum_{i=1}^{d}|i\rangle\otimes|i\rangle$, which is deliberately unnormalized. Then
--
--   $$(I\otimes X)|\widetilde\psi^+\rangle=(X^T\otimes I)|\widetilde\psi^+\rangle.$$
--
--   Transposition is relative to that basis, and $X$ need not satisfy any positivity, Hermiticity, unitarity or trace-preservation condition. The identity transfers an operator across the two entangled factors.
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 21, Lemma 12: transpose identity for an unnormalized maximally entangled vector

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 12, PDF p.21 Eq.(B2): arbitrary X, transpose in the common
computational orthonormal basis, and the deliberately unnormalized Bell vector. -/
theorem bell_transpose_identity (d : ℕ) (hd : 2 ≤ d) (X : Matrix (Fin d) (Fin d) ℂ) :
    act (Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ) X) (unnormalizedBell d) =
      act (Matrix.kronecker Xᵀ (1 : Matrix (Fin d) (Fin d) ℂ)) (unnormalizedBell d) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
