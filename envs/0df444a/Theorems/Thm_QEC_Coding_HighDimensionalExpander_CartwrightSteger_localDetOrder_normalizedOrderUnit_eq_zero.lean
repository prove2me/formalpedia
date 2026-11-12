-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_localDetOrder_normalizedOrderUnit_eq_zero
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.localDetOrder_normalizedOrderUnit_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:45:31.112445+00:00
-- url     : https://prove2.me/theorems/10293c50-da07-41a8-96a4-5a22f813aa5a
-- title:
--   Cartwright Steger: local Det Order normalized Order Unit eq zero
-- statement:
--   The Cartwright Steger construction uses the local Det Order normalized Order Unit eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L141-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L141-L164

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.localDetOrder_normalizedOrderUnit_eq_zero
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ)
    (hq : SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u))) =
      (r.matrixRank : ℤ) * q) :
    SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (cyclicUnitToBuildingGL P r
            (orderUnitToCyclicUnit P r
              (normalizedOrderUnit P r u q)))) = 0 := by sorry
