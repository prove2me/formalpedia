-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_eq_constantConjugatedB
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_eq_constantConjugatedB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:40.500981+00:00
-- url     : https://prove2.me/theorems/39a941d1-904e-450f-9026-5a9dc1f7a381
-- title:
--   Cartwright Steger: cartwright Steger Generator eq constant Conjugated B
-- statement:
--   The arbitrary-unit conjugate specializes definitionally to every
--   construction-owned Cartwright--Steger generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L455-L460
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L455-L460

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_eq_constantConjugatedB
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    cartwrightStegerGenerator P r x =
      constantConjugatedCartwrightStegerB P r
        (constantClassRepresentative P r x) := by sorry
