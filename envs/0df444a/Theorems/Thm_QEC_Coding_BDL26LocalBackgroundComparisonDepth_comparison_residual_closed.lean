-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_comparison_residual_closed
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonDepth.comparison_residual_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:29:47.797026+00:00
-- url     : https://prove2.me/theorems/5b86988c-2213-42bb-86cb-9e76b53a211d
-- title:
--   BDL26 Local Background Comparison Depth: comparison residual closed
-- statement:
--   Every comparison residual is a genuine full top cocycle. Thus the
--   nonboundary conclusions below concern logical classes, not nonclosed words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L27-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L27-L40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalBackgroundComparisonDepth.comparison_residual_closed (S : OddScale) (n : Nat)
    (sigma : TopInput S n) (e : W S n) :
    (SuffixData S n).family.coboundary1 (TopIndex n)
      (BDL26AllDepthBottomComparisonStability.residual S n sigma e)=0 := by sorry
