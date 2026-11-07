-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityDefectTailTerm_zero
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityDefectTailTerm_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:04:06.103856+00:00
-- url     : https://prove2.me/theorems/43566c45-3746-4ae1-9aeb-9ad77e19ac9c
-- title:
--   Cartwright Steger: infinity Defect Tail Term zero
-- statement:
--   The zeroth predecessor summand is exactly the non-tail defect.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1045-L1052
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L1045-L1052

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityDefectTailTerm_zero
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityDefectTailTerm P r u k 0 ζ =
      infinityDefectMonomial P r u k ζ := by sorry
