-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_globalCyclicZ
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_globalCyclicZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:26:34.533199+00:00
-- url     : https://prove2.me/theorems/b9b8a489-d1b6-4203-8eb6-b1e44a04cb49
-- title:
--   Cartwright Steger: cyclic Algebra To Building global Cyclic Z
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra To Building global Cyclic Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCompatibility.lean#L74-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCompatibility.lean#L74-L108

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_OrderUnitReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_globalCyclicZ
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ) :
    cyclicAlgebraToBuilding P r
        ⟨globalCyclicZMatrixHom P r n,
          globalCyclicZMatrixHom_mem_cyclicAlgebra P r n⟩ =
      buildingCyclicZMatrixHom P r n := by sorry
