-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_incidentHamiltonian_supported
-- name    : QEC.Coding.BDL26CSSDaviesLocality.incidentHamiltonian_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:40:08.539199+00:00
-- url     : https://prove2.me/theorems/dc5bd5c9-9e5d-44f7-93d8-1002bf52810f
-- title:
--   BDL26 CSSDavies Locality: incident Hamiltonian supported
-- statement:
--   The BDL26 CSSDavies Locality construction uses the incident Hamiltonian supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L127-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L127-L129

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_incidentHamiltonian_supported

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.incidentHamiltonian_supported (q : Physical S n) :
    (subsystem S n q).OperatorSupportedOnRegister (incidentHamiltonian S n q) := by sorry
