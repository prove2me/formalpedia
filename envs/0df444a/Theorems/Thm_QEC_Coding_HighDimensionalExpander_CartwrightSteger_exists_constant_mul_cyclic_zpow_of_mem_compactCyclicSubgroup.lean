-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_constant_mul_cyclic_zpow_of_mem_compactCyclicSubgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_constant_mul_cyclic_zpow_of_mem_compactCyclicSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:02:00.352143+00:00
-- url     : https://prove2.me/theorems/10d8f912-53f0-49a3-b224-0685f685428d
-- title:
--   Cartwright Steger: exists constant mul cyclic zpow of mem compact Cyclic Subgroup
-- statement:
--   Every element of the explicit compact cyclic subgroup has a genuine
--   `u z^n` normal form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L644-L656
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L644-L656

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_constant_mul_cyclic_zpow_of_mem_compactCyclicSubgroup
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hg : g ∈ BuildingCompactCyclicSubgroup P r) :
    ∃ u : (ConstantExtension P r)ˣ, ∃ n : ℤ,
      g = buildingConstantPGLHom P r u *
        buildingCyclicGeneratorPGL P r ^ n := by sorry
