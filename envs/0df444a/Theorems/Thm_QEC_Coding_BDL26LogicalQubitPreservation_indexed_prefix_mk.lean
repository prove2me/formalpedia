-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_indexed_prefix_mk
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.indexed_prefix_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:56:32.180248+00:00
-- url     : https://prove2.me/theorems/679f76e7-a9ff-4b0c-be31-6d02b2a0aebb
-- title:
--   BDL26 Logical Qubit Preservation: indexed prefix mk
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the indexed prefix mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L195-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L195-L199

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.indexed_prefix_mk (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : BDL26FiniteCohomology.Cocycle S 0) :
    indexedLogicalEquiv S depth i
      (logicalClass S i.val (prefixRepresentative S i.val w)) =
      BDL26SeedCohomology.coefficient w.1 := by sorry
