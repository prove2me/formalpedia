-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_indexed_right_inverse
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.indexed_right_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:56:01.645326+00:00
-- url     : https://prove2.me/theorems/3bdd7e92-4fa7-4ec2-b3b8-d9bac39330e7
-- title:
--   BDL26 Logical Qubit Preservation: indexed right inverse
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the indexed right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L191-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L191-L193

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_indexed_right_inverse
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.indexed_right_inverse (S : OddScale) (depth : Nat) (i : LevelIndex depth) (c : Field) :
    indexedLogicalEquiv S depth i ((indexedLogicalEquiv S depth i).symm c) = c := by sorry
