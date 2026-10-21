-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_pure_output_spectrum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.pure_output_spectrum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:38:11.137996+00:00
-- url     : https://prove2.me/theorems/48b253dd-c377-4598-8db9-c33918bc94ef
-- title:
--   Pure-input nonzero output spectra agree
-- statement:
--   Let $V:H_A\to H_B\otimes H_C$ be an arbitrary linear map between finite complex Hilbert spaces with $H_A\ne0$. For any vector $\psi\in H_A$, put $X_B=\operatorname{Tr}_C V|\psi\rangle\langle\psi|V^*$ and $X_C=\operatorname{Tr}_B V|\psi\rangle\langle\psi|V^*$. Both are Hermitian and
--
--   $$\operatorname{spec}_{\ne0}(X_B)=\operatorname{spec}_{\ne0}(X_C)$$
--
--   as multisets, retaining every nonzero eigenvalue's multiplicity. Neither $V$ nor its output vector must preserve norm, and zero eigenvalues are ignored when output dimensions differ. This is the spectral observation underlying complementary output-purity identities.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 3, Pure-input nonzero output spectra agree

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- Theorem 1 proof, PDF p.3: psi and V need NOT be normalized. -/
theorem pure_output_spectrum [Nonempty A] (V : Matrix (B × C) A ℂ) (psi : EuclideanSpace ℂ A) :
    (receiverChannel V (pureDensity psi)).IsHermitian ∧
    (complementaryChannel V (pureDensity psi)).IsHermitian ∧
    nonzeroSpectrum (receiverChannel V (pureDensity psi)) =
      nonzeroSpectrum (complementaryChannel V (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
