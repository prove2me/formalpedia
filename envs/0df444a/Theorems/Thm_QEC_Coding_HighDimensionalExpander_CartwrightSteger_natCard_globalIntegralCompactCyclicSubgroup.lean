-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_globalIntegralCompactCyclicSubgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_globalIntegralCompactCyclicSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:05:05.889867+00:00
-- url     : https://prove2.me/theorems/653ac0ae-c0e5-47a0-8760-5d96360524da
-- title:
--   Cartwright Steger: nat Card global Integral Compact Cyclic Subgroup
-- statement:
--   The Cartwright Steger construction uses the nat Card global Integral Compact Cyclic Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/CompactNormalForm.lean#L416-L422
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/CompactNormalForm.lean#L416-L422

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactGroup
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_globalIntegralCompactCyclicSubgroup
    (P : BasePrime) (r : Rank) :
    Nat.card (GlobalIntegralCompactCyclicSubgroup P r) =
      r.matrixRank * ∑ i ∈ Finset.range r.matrixRank, P.q ^ i := by sorry
