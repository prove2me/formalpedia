-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_indexed_symm_scalar
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.indexed_symm_scalar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:56:25.020903+00:00
-- url     : https://prove2.me/theorems/11d5410e-6a38-43e0-9ebc-66282d816468
-- title:
--   BDL26 Logical Qubit Preservation: indexed symm scalar
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the indexed symm scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L201-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L201-L204

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.indexed_symm_scalar (S : OddScale) (depth : Nat) (i : LevelIndex depth) (c : Field) :
    (indexedLogicalEquiv S depth i).symm c = logicalClass S i.val
      (prefixRepresentative S i.val (c • BDL26SeedCohomology.seedElement)) := by sorry
