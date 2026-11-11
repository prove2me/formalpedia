-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_indexed_step_word
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.indexed_step_word
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:56:47.577193+00:00
-- url     : https://prove2.me/theorems/48b94274-e519-4022-827f-5bce8a921e9b
-- title:
--   BDL26 Logical Qubit Preservation: indexed step word
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the indexed step word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L217-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L217-L222

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.indexed_step_word (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleBoundaryCode.dual.carrier) :
    (stepRepresentative S i.val w).1 =
      ((indexedDecoderData S depth).selectedMap i).map1 w.1 := by sorry
