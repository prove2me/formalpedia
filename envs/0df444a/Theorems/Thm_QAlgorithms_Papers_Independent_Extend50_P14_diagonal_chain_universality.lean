-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_diagonal_chain_universality
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.diagonal_chain_universality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:10:00.859921+00:00
-- url     : https://prove2.me/theorems/460c6a57-97b0-4b75-9ee1-7cc937e9c5f8
-- title:
--   Theorem 11: diagonal controls and adjacent exchange
-- statement:
--   On n≥1 qubits let D be all diagonal Hermitian controls and R_{j,j+1}=(X_jX_{j+1}+Y_jY_{j+1})/2 for 1≤j<n. Then
--
--   $$\operatorname{Lie}_{\mathbb R}\{iD,\ iR_{j,j+1}:1\le j<n\}=\{A:A^\dagger=-A,\ [A,\sum_j Z_j]=0\}.$$
--
--   For one qubit the exchange family is empty and diagonal controls already give the full invariant algebra.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 28, Theorem 11: diagonal controls and nearest-neighbor exchange generate all U(1) Hamiltonians

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.28–29, Theorem 11/C34: adjacent exchange plus all diagonal controls.
For n=1 the exchange family is empty and diagonal controls already suffice. -/
theorem diagonal_chain_universality (n : ℕ) (hn : 1 ≤ n) :
    (LieSubalgebra.lieSpan ℝ (QMat n)
      ((fun H => Complex.I • H) '' diagonalChainControls n) : Set (QMat n)) =
      {A | A + Aᴴ = 0 ∧ U1Invariant A} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
