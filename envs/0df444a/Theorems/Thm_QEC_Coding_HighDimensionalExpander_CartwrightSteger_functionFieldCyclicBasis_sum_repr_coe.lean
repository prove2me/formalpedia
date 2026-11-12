-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_sum_repr_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldCyclicBasis_sum_repr_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:14:11.72572+00:00
-- url     : https://prove2.me/theorems/3e149992-f300-4ffc-8a02-18ad0c2dde8d
-- title:
--   Cartwright Steger: function Field Cyclic Basis sum repr coe
-- statement:
--   The Cartwright Steger construction uses the function Field Cyclic Basis sum repr coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstructionTheorem.lean#L38-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstructionTheorem.lean#L38-L55

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldCyclicBasis_sum_repr_coe
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    (∑ p, (functionFieldCyclicBasis P r).repr x p •
        (functionFieldCyclicBasisVector P r p :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))) = x.1 := by sorry
