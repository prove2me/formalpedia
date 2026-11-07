-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantConjugatedCartwrightStegerB_val
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:08.675107+00:00
-- url     : https://prove2.me/theorems/4b6b6dfc-cffb-4937-a716-913e0e92e4ea
-- title:
--   Cartwright Steger: constant Conjugated Cartwright Steger B val
-- statement:
--   The conjugated generator itself is `1 - (u / phi⁻¹(u)) z⁻¹` in the
--   constructed global matrix algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L496-L537
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L496-L537

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedCartwrightStegerB_val
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (constantConjugatedCartwrightStegerB P r u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      1 - constantMatrix P r (infinityCyclicInverseCoefficient P r u) *
        cyclicGeneratorInverseMatrix P r := by sorry
