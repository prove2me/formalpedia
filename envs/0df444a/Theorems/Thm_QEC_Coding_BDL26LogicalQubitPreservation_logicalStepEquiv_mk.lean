-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalStepEquiv_mk
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.logicalStepEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:40:48.684891+00:00
-- url     : https://prove2.me/theorems/adaad718-1d31-46b5-897c-d99ae76c5b2b
-- title:
--   BDL26 Logical Qubit Preservation: logical Step Equiv mk
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the logical Step Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L162-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L162-L171

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.logicalStepEquiv_mk (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalStepEquiv S n (logicalClass S n w) =
      logicalClass S (n+1) (stepRepresentative S n w) := by sorry
