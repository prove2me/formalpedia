-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_indexed_step_mk
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.indexed_step_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:56:59.421043+00:00
-- url     : https://prove2.me/theorems/36ff3404-4e6b-4e37-8a91-60970781073f
-- title:
--   BDL26 Logical Qubit Preservation: indexed step mk
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the indexed step mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L211-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L211-L215

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.indexed_step_mk (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleBoundaryCode.dual.carrier) :
    indexedLogicalStepEquiv S depth i (logicalClass S i.val w) =
      logicalClass S (i.val+1) (stepRepresentative S i.val w) := by sorry
