-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logical_left_inverse
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.logical_left_inverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:46:01.617489+00:00
-- url     : https://prove2.me/theorems/9676dfc3-1920-4324-b6b4-328df65fdc53
-- title:
--   BDL26 Logical Qubit Preservation: logical left inverse
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the logical left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L71-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L71-L73

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.logical_left_inverse (S : OddScale) (n : Nat) (v : LogicalQuotient S n) :
    (logicalEquiv S n).symm (logicalEquiv S n v) = v := by sorry
