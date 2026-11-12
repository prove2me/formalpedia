-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReduction_generatorRatio_mem_subgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_generatorRatio_mem_subgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:50:19.322551+00:00
-- url     : https://prove2.me/theorems/551f4329-a174-4f5d-aa19-d8b11b5736d5
-- title:
--   Cartwright Steger: order Norm One Inner Form Reduction generator Ratio mem subgroup
-- statement:
--   The Cartwright Steger construction uses the order Norm One Inner Form Reduction generator Ratio mem subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3949-L3956
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3949-L3956

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_generatorRatio_mem_subgroup
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : ConstantProjectiveClass P r) :
    orderNormOneInnerFormReduction P r level
        (orderNormOneGeneratorRatio P r u v) ∈
      IndexNormOneGeneratorRatioSubgroup P r level := by sorry
