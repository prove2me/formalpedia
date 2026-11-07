-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantPGL_mem_compactCyclicSubgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGL_mem_compactCyclicSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:58:59.316062+00:00
-- url     : https://prove2.me/theorems/a997729b-c904-4e72-b644-a66e11be399e
-- title:
--   Cartwright Steger: building Constant PGL mem compact Cyclic Subgroup
-- statement:
--   The Cartwright Steger construction uses the building Constant PGL mem compact Cyclic Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L607-L610
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L607-L610

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGL_mem_compactCyclicSubgroup
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingConstantPGLHom P r u ∈ BuildingCompactCyclicSubgroup P r := by sorry
