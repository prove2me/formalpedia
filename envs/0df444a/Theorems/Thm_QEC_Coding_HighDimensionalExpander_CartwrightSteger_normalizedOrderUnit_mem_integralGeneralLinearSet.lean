-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_normalizedOrderUnit_mem_integralGeneralLinearSet
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalizedOrderUnit_mem_integralGeneralLinearSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:45:14.578446+00:00
-- url     : https://prove2.me/theorems/5850dd6d-ae9e-40c1-bfc3-871016711189
-- title:
--   Cartwright Steger: normalized Order Unit mem integral General Linear Set
-- statement:
--   The Cartwright Steger construction uses the normalized Order Unit mem integral General Linear Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L166-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L166-L191

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalizedOrderUnit_mem_integralGeneralLinearSet
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank)
    (hq : SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u))) =
      (r.matrixRank : ℤ) * q) :
    cyclicUnitToBuildingGL P r
        (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q)) ∈
      SphericalHecke.integralGeneralLinearSet
        (BaseField P) r.matrixRank := by sorry
