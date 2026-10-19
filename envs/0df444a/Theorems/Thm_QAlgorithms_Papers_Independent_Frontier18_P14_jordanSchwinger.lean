-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_jordanSchwinger
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.jordanSchwinger
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:03:46.747265+00:00
-- url     : https://prove2.me/theorems/236ee5ec-ee82-40bf-9711-aac659c9f079
-- title:
--   Jordan–Schwinger commutators and Casimir
-- statement:
--   On the common finite-occupation core of two bosonic modes, define $L_t=(a_1^\dagger a_1+a_2^\dagger a_2)/2$, $L_x=(a_1^\dagger a_2+a_2^\dagger a_1)/2$, $L_y=i(a_2^\dagger a_1-a_1^\dagger a_2)/2$, and $L_z=(a_1^\dagger a_1-a_2^\dagger a_2)/2$. Then
--
--   $$[L_x,L_y]=iL_z,\quad[L_y,L_z]=iL_x,\quad[L_z,L_x]=iL_y,\qquad L_x^2+L_y^2+L_z^2=L_t(L_t+I).$$
--
--   Moreover $L_t$ commutes with $L_x,L_y,L_z$. These are polynomial operator identities on the invariant core, giving the angular-momentum representation of the two modes; no boundedness of the full Fock operators is assumed.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 19, §4.2: Jordan–Schwinger commutators and Casimir

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.17,19, (4.6)–(4.8): all identities are equalities of operators
on the common invariant finite-occupation core of full two-mode Fock space. -/
theorem jordanSchwinger :
    commutator stokesX stokesY = Complex.I • stokesZ ∧
    commutator stokesY stokesZ = Complex.I • stokesX ∧
    commutator stokesZ stokesX = Complex.I • stokesY ∧
    commutator stokesT stokesX = 0 ∧
    commutator stokesT stokesY = 0 ∧
    commutator stokesT stokesZ = 0 ∧
    stokesX ^ 2 + stokesY ^ 2 + stokesZ ^ 2 = stokesT * (stokesT + 1) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
