-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_BuildingCompactCyclicSubgroup_le_maximalCompact
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.BuildingCompactCyclicSubgroup_le_maximalCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:20:06.331922+00:00
-- url     : https://prove2.me/theorems/060ef55a-245b-4f4b-ad98-07fc3c6d71bd
-- title:
--   Cartwright Steger: Building Compact Cyclic Subgroup le maximal Compact
-- statement:
--   The explicit constant/cyclic subgroup really is compact: every one of
--   its generators lies in the maximal compact subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L710-L721
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L710-L721

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.BuildingCompactCyclicSubgroup_le_maximalCompact
    (P : BasePrime) (r : Rank) :
    BuildingCompactCyclicSubgroup P r ≤
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by sorry
