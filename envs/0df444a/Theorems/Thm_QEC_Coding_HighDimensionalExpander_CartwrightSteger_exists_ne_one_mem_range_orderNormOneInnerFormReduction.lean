-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_ne_one_mem_range_orderNormOneInnerFormReduction
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_ne_one_mem_range_orderNormOneInnerFormReduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:39:50.279697+00:00
-- url     : https://prove2.me/theorems/c4da6704-6dca-41e9-a431-30b8a0c71ec3
-- title:
--   Cartwright Steger: exists ne one mem range order Norm One Inner Form Reduction
-- statement:
--   The genuine norm-one reduction has a construction-owned nonidentity
--   element, namely the ratio of two distinct Cartwright--Steger generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3889-L3912
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3889-L3912

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_ne_one_mem_range_orderNormOneInnerFormReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    ∃ g : PSL P r level,
      g ∈ (orderNormOneInnerFormReduction P r level).range ∧ g ≠ 1 := by sorry
