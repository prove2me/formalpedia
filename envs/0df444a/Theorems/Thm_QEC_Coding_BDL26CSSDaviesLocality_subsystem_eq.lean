-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_subsystem_eq
-- name    : QEC.Coding.BDL26CSSDaviesLocality.subsystem_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:36:08.668612+00:00
-- url     : https://prove2.me/theorems/788b6fa1-9a0f-4f4f-b7b6-b02e47399f97
-- title:
--   BDL26 CSSDavies Locality: subsystem eq
-- statement:
--   The BDL26 CSSDavies Locality construction uses the subsystem eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L45-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L45-L47

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

theorem QEC.Coding.BDL26CSSDaviesLocality.subsystem_eq (q : Physical S n) :
    CSSDaviesLocality.subsystem (zSyndrome S n) (xSyndrome S n) q =
      subsystem S n q := by sorry
