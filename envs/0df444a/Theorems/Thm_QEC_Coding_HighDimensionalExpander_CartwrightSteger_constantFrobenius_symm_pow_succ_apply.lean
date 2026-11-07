-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_symm_pow_succ_apply
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_symm_pow_succ_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:02:30.793311+00:00
-- url     : https://prove2.me/theorems/1db52a46-51b6-4c6c-a43e-37a9a7ec5529
-- title:
--   Cartwright Steger: constant Frobenius symm pow succ apply
-- statement:
--   Applying inverse Frobenius removes one positive Frobenius step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L283-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L283-L297

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_symm_pow_succ_apply
    (P : BasePrime) (r : Rank) (n : ℕ) (c : ConstantExtension P r) :
    (constantFrobenius P r).symm
        ((constantFrobenius P r ^ (n + 1)) c) =
      (constantFrobenius P r ^ n) c := by sorry
