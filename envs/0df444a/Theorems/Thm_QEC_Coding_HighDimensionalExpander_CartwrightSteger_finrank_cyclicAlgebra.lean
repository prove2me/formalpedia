-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_finrank_cyclicAlgebra
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.finrank_cyclicAlgebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:47:26.042583+00:00
-- url     : https://prove2.me/theorems/71592ad0-e107-4e7b-8db7-5d09ff591ef0
-- title:
--   Cartwright Steger: finrank cyclic Algebra
-- statement:
--   The central division algebra has degree exactly the selected matrix rank:
--   its dimension over the global function field is `d²`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicDivisionAlgebra.lean#L168-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicDivisionAlgebra.lean#L168-L173

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.finrank_cyclicAlgebra
    (P : BasePrime) (r : Rank) :
    Module.finrank (FunctionField P) (CyclicAlgebra P r) =
      r.matrixRank * r.matrixRank := by sorry
