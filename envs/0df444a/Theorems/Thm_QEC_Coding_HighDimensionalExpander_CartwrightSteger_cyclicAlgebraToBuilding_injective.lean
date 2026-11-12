-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:47:46.659223+00:00
-- url     : https://prove2.me/theorems/34da4f05-feb0-427a-b846-60feac6a4855
-- title:
--   Cartwright Steger: cyclic Algebra To Building injective
-- statement:
--   The explicit representation at the building place is faithful.  This is
--   now a consequence of the proved division-ring structure, not an assumption
--   about the displayed matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicDivisionAlgebra.lean#L178-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicDivisionAlgebra.lean#L178-L182

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cyclicAlgebraToBuilding P r) := by sorry
