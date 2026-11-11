-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_indexed_left_inverse
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.indexed_left_inverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:54:54.724803+00:00
-- url     : https://prove2.me/theorems/815d51f4-d984-4bba-bc35-e37e816124a7
-- title:
--   BDL26 Logical Qubit Preservation: indexed left inverse
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the indexed left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L186-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L186-L189

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_indexed_left_inverse
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.indexed_left_inverse (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : ((indexedFamily S depth).complex i).pureXLogicalQuotient) :
    (indexedLogicalEquiv S depth i).symm (indexedLogicalEquiv S depth i w) = w := by sorry
