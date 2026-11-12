-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicUnitToBuildingGL_orderYUnit
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicUnitToBuildingGL_orderYUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:43:12.991982+00:00
-- url     : https://prove2.me/theorems/0c822bcb-4d13-49b2-b6da-24a0c19360af
-- title:
--   Cartwright Steger: cyclic Unit To Building GL order YUnit
-- statement:
--   The Cartwright Steger construction uses the cyclic Unit To Building GL order YUnit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L50-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L50-L78

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicUnitToBuildingGL_orderYUnit
    (P : BasePrime) (r : Rank) :
    cyclicUnitToBuildingGL P r
        (orderUnitToCyclicUnit P r (cartwrightStegerOrderYUnit P r)) =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (buildingLocalYUnit P) := by sorry
