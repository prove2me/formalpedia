-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityDefectTailTerm_rank
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityDefectTailTerm_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:50.160195+00:00
-- url     : https://prove2.me/theorems/051108f5-f9ab-4d0f-afc7-5f7f7e03d3f0
-- title:
--   Cartwright Steger: infinity Defect Tail Term rank
-- statement:
--   The omitted terminal predecessor is the initial predecessor multiplied
--   by the central wrap factor `1 + y`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L985-L994
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L985-L994

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityDefectTailTerm_rank
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityDefectTailTerm P r u k r.matrixRank ζ =
      (onePlusY P r) • infinityDefectTailTerm P r u k 0 ζ := by sorry
