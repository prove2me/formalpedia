-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicUnitToBuildingGL_normalizedOrderUnit
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicUnitToBuildingGL_normalizedOrderUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:44:11.237953+00:00
-- url     : https://prove2.me/theorems/b8a63e2a-f0a7-4ac7-9af6-414eb4dfc699
-- title:
--   Cartwright Steger: cyclic Unit To Building GL normalized Order Unit
-- statement:
--   The Cartwright Steger construction uses the cyclic Unit To Building GL normalized Order Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L101-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L101-L110

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicUnitToBuildingGL_normalizedOrderUnit
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ) :
    cyclicUnitToBuildingGL P r
        (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q)) =
      (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
          (buildingLocalYUnit P)) ^ (-q) *
        cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u) := by sorry
