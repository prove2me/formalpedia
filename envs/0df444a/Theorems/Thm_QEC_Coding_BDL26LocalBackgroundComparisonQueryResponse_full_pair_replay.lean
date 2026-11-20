-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_full_pair_replay
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.full_pair_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:37:02.423188+00:00
-- url     : https://prove2.me/theorems/328a70bc-9faa-46f8-9c5e-3ee66c21be2c
-- title:
--   BDL26 Local Background Comparison Query Response: full pair replay
-- statement:
--   Full paired correction equality; both genuine C2 calls are retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L114-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L114-L184

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.full_pair_replay (s t : TopInput S n) (e : W S n)
    (a : LevelIndex n)
    (hstop : a.val = 0 ∨ actualInputs S n s a = actualInputs S n (perturbTop S n s e) a)
    (ha : AgreeOn (queries S n e a (TopIndex n)) s.val t.val) :
    BDL26AllDepthBottomComparisonStability.correction S n s +
        BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n s e) =
      BDL26AllDepthBottomComparisonStability.correction S n t +
        BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n t e) := by sorry
