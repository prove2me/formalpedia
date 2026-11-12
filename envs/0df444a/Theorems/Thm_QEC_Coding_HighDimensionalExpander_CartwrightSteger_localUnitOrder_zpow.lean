-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_localUnitOrder_zpow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.localUnitOrder_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:45:26.983433+00:00
-- url     : https://prove2.me/theorems/9cbc2f8b-d08c-44a9-991b-07f90e6f97a4
-- title:
--   Cartwright Steger: local Unit Order zpow
-- statement:
--   The Cartwright Steger construction uses the local Unit Order zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L127-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L127-L139

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.localUnitOrder_zpow
    (P : BasePrime) (a : (BuildingLocalField P)ˣ) (n : ℤ) :
    SphericalHecke.localUnitOrder (a ^ n) =
      n * SphericalHecke.localUnitOrder a := by sorry
