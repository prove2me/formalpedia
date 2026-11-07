-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_buildingCompactCyclicSubgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_buildingCompactCyclicSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:29:55.448804+00:00
-- url     : https://prove2.me/theorems/f34d8970-eaf2-48b1-bacb-ab096bfd218d
-- title:
--   Cartwright Steger: nat Card building Compact Cyclic Subgroup
-- statement:
--   The Cartwright Steger construction uses the nat Card building Compact Cyclic Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCompactNormalForm.lean#L265-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCompactNormalForm.lean#L265-L270

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCompactNormalForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_buildingCompactCyclicSubgroup
    (P : BasePrime) (r : Rank) :
    Nat.card (BuildingCompactCyclicSubgroup P r) =
      r.matrixRank * ∑ i ∈ Finset.range r.matrixRank, P.q ^ i := by sorry
