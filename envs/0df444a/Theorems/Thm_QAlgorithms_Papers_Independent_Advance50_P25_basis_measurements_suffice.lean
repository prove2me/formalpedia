-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_basis_measurements_suffice
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.basis_measurements_suffice
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:51:15.277998+00:00
-- url     : https://prove2.me/theorems/b1749a14-220f-40b2-81a0-aeb1dd3162bd
-- title:
--   All basis measurements suffice to test firm subadditivity
-- statement:
--   Let $S_K$ be a concave spectral entropy family on finite-dimensional density operators, zero on pure states and invariant under adjoining zero eigenvalues. Define $I_K(a:b)$ from the two marginal entropies minus the joint entropy, and define $\chi_K$ using normalized conditional states.
--
--   The following universal conditions are equivalent:
--
--   $$
--   \bigl[\forall\rho_{ab},w_a:\ \chi_K(w_a,b)\le I_K(a:b)\bigr]
--   \quad\Longleftrightarrow\quad
--   \bigl[\forall\rho_{ab},P_a:\ \chi_K(P_a,b)\le I_K(a:b)\bigr].
--   $$
--
--   Here both sides range over every finite positive pair of system dimensions and every normalized bipartite density. The measurement $w_a$ is any orthonormal-basis projective measurement, whereas $P_a$ is any finite POVM. The basis premise includes enlarged dimensions used for Naimark extensions.
--
--   Thus basis measurements suffice to test the global FSA property.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 2, §III, unnumbered: testing all orthonormal bases suffices for FSA

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF pp.2–3, §III: testing all basis measurements in all dimensions suffices. -/
theorem basis_measurements_suffice (S : EntropyFunction) (hS : IsEntropy S) :
    BasisFirmlySubadditive S ↔ FirmlySubadditive S := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end
