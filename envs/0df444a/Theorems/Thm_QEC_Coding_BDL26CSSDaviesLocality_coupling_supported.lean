-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_supported
-- name    : QEC.Coding.BDL26CSSDaviesLocality.coupling_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:39:55.262684+00:00
-- url     : https://prove2.me/theorems/21aa0cde-67d5-49d9-b380-36e81fcd3337
-- title:
--   BDL26 CSSDavies Locality: coupling supported
-- statement:
--   The BDL26 CSSDavies Locality construction uses the coupling supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L131-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L131-L133

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_coupling_supported

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.coupling_supported (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    (subsystem S n q).OperatorSupportedOnRegister (coupling S n q a) := by sorry
