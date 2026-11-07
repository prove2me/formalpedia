-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_inv_val
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_inv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:47.264216+00:00
-- url     : https://prove2.me/theorems/13a04a9d-979e-4553-b282-7a0bdfb10ba9
-- title:
--   Cartwright Steger: constant Conjugated Cartwright Steger B inv val
-- statement:
--   LSV05b's displayed inverse formula for every constant conjugate of
--   `b`, proved in the constructed global matrix algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L627-L695
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L627-L695

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_inv_val
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      constantConjugatedBInverseExpansion P r u := by sorry
