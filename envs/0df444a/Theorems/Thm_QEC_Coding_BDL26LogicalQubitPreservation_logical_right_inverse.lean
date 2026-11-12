-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logical_right_inverse
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.logical_right_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:45:06.047552+00:00
-- url     : https://prove2.me/theorems/0f734a7d-6eab-4a6d-a209-44a7c619c912
-- title:
--   BDL26 Logical Qubit Preservation: logical right inverse
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the logical right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L75-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L75-L77

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.logical_right_inverse (S : OddScale) (n : Nat) (c : Field) :
    logicalEquiv S n ((logicalEquiv S n).symm c) = c := by sorry
