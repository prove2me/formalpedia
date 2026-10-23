-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_pure_output_spectrum
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.pure_output_spectrum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:53:23.00862+00:00
-- url     : https://prove2.me/theorems/f00e530a-a5f0-4e63-ba4d-b02f10096809
-- title:
--   Theorem 3: equal nonzero output spectra on pure inputs
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. For conjugate channels $\Phi,\Phi^C$ and every unit vector $\psi$, the eigenvalue multisets, counting multiplicities and deleting only zeros, satisfy
--
--   $$
--   \operatorname{spec}_{\ne0}\Phi(|\psi\rangle\langle\psi|)=\operatorname{spec}_{\ne0}\Phi^C(|\psi\rangle\langle\psi|).
--   $$
--
--   Deleting zeros permits different output dimensions.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 7, Theorem 3: equal nonzero output spectra on pure inputs

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- Theorem 3, PDF pp.7–8: spectrum with multiplicities; only zeros are discarded. -/
theorem pure_output_spectrum [Nonempty A] [Nonempty B] [Nonempty C]
    (Phi : Superop A B) (PhiC : Superop A C) (hPhi : IsChannel Phi)
    (hc : CPComplementary Phi PhiC) (psi : EuclideanSpace ℂ A) (hpsi : IsState psi) :
    nonzeroSpectrum (Phi (pureDensity psi)) = nonzeroSpectrum (PhiC (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
