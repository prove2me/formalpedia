-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_frequency_eq_incident
-- name    : QEC.Coding.BDL26CSSDaviesLocality.frequency_eq_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:38:56.162958+00:00
-- url     : https://prove2.me/theorems/7ce52224-a220-4582-b310-77bbdf3f5e69
-- title:
--   BDL26 CSSDavies Locality: frequency eq incident
-- statement:
--   Complementary check terms change no coherent frequency component.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L119-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L119-L125

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_eq_incident
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.frequency_eq_incident (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
      (coupling S n q a) ω =
    actualFrequency (incidentHamiltonian S n q) (incidentHamiltonian_symmetric S n q)
      (coupling S n q a) ω := by sorry
