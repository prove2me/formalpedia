-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderToCyclicAlgebra_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderToCyclicAlgebra_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:20:52.87221+00:00
-- url     : https://prove2.me/theorems/fbc559e5-be61-4dbe-8930-05f241617b4c
-- title:
--   Cartwright Steger: cartwright Steger Order To Cyclic Algebra injective
-- statement:
--   The Cartwright Steger construction uses the cartwright Steger Order To Cyclic Algebra injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L64-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean#L64-L78

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderToCyclicAlgebra_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cartwrightStegerOrderToCyclicAlgebra P r) := by sorry
