-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityLeadingTailTerm_sub_defectTailTerm_succ
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLeadingTailTerm_sub_defectTailTerm_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:34.54803+00:00
-- url     : https://prove2.me/theorems/f469a586-30a9-404d-a078-259e11809594
-- title:
--   Cartwright Steger: infinity Leading Tail Term sub defect Tail Term succ
-- statement:
--   Pairing a leading tail term with the next predecessor term produces
--   one shifted equation-(9) correction term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L946-L981
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L946-L981

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLeadingTailTerm_sub_defectTailTerm_succ
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    infinityLeadingTailTerm P r u k i ζ -
        infinityDefectTailTerm P r u k (i + 1) ζ =
      infinityShiftedCorrectionTerm P r u k i ζ := by sorry
