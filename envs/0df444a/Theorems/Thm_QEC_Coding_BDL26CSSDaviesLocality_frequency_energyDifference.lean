-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_frequency_energyDifference
-- name    : QEC.Coding.BDL26CSSDaviesLocality.frequency_energyDifference
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:40:11.389193+00:00
-- url     : https://prove2.me/theorems/b0b2677c-eb72-4594-ae7e-0ca3aad21640
-- title:
--   BDL26 CSSDavies Locality: frequency energy Difference
-- statement:
--   Energy transferred to the bath is the right-energy minus left-energy gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L144-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L144-L152

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.frequency_energyDifference (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω * BDL26CSSHamiltonian.hamiltonian S n -
      BDL26CSSHamiltonian.hamiltonian S n *
        actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω =
    (ω : ℂ) • actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
      (coupling S n q a) ω := by sorry
