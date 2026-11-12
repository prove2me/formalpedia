-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_indexedLogicalEquiv_mk
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.indexedLogicalEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:52:01.381644+00:00
-- url     : https://prove2.me/theorems/7d4612bd-27ef-4bf4-855d-ce3554c4de24
-- title:
--   BDL26 Logical Qubit Preservation: indexed Logical Equiv mk
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the indexed Logical Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L178-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L178-L184

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.indexedLogicalEquiv_mk (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : ((indexedFamily S depth).complex i).middleBoundaryCode.dual.carrier) :
    indexedLogicalEquiv S depth i
      (((indexedFamily S depth).complex i).firstCoboundaryInMiddleBoundaryDual.mkQ w) =
      BDL26FiniteCohomology.indexedEquiv S depth i
        (((indexedFamily S depth).complex i).middleCoboundaryInCocycles.mkQ
          (cocycleEquiv S i.val w)) := by sorry
