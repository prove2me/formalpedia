-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_right_inverse
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.suffix_right_inverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T19:02:25.793199+00:00
-- url     : https://prove2.me/theorems/96f4611a-9e24-4964-a808-871f99028908
-- title:
--   BDL26 History Logical Residual: suffix right inverse
-- statement:
--   The BDL26 History Logical Residual construction uses the suffix right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L96-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L96-L98

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryLogicalResidual.suffix_right_inverse (a b : LevelIndex n) (x : FC.H1 S (b.val+2)) :
    suffixEquiv S n a b ((suffixEquiv S n a b).symm x) = x := by sorry
