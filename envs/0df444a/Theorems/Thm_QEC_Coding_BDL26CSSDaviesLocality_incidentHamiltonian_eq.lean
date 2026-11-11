-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_incidentHamiltonian_eq
-- name    : QEC.Coding.BDL26CSSDaviesLocality.incidentHamiltonian_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:36:17.749122+00:00
-- url     : https://prove2.me/theorems/b53f780f-7670-4492-b75b-e7981958157e
-- title:
--   BDL26 CSSDavies Locality: incident Hamiltonian eq
-- statement:
--   The BDL26 CSSDavies Locality construction uses the incident Hamiltonian eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L57-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L57-L59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.incidentHamiltonian_eq (q : Physical S n) :
    CSSDaviesLocality.incidentHamiltonian (zSyndrome S n) (xSyndrome S n) q =
      incidentHamiltonian S n q := by sorry
