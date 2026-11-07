-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:18.507696+00:00
-- url     : https://prove2.me/theorems/14778169-d8fa-4810-97e0-9053a5fdb1ab
-- title:
--   Cartwright Steger: exists constant mul cyclic pow of mem compact Cyclic Subgroup
-- statement:
--   Projective scalar reduction makes the cyclic exponent unique up to the
--   matrix rank, so every compact normal form can be chosen in
--   `0 ≤ j < matrixRank`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L661-L689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L661-L689

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hg : g ∈ BuildingCompactCyclicSubgroup P r) :
    ∃ u : (ConstantExtension P r)ˣ, ∃ j : ℕ, j < r.matrixRank ∧
      g = buildingConstantPGLHom P r u *
        buildingCyclicGeneratorPGL P r ^ j := by sorry
