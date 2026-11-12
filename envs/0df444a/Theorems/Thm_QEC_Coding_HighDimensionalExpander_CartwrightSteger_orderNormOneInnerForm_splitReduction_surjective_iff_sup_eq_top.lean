-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerForm_splitReduction_surjective_iff_sup_eq_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerForm_splitReduction_surjective_iff_sup_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:09:23.21342+00:00
-- url     : https://prove2.me/theorems/2585e122-759a-4634-8202-3663abcbe9ef
-- title:
--   Cartwright Steger: order Norm One Inner Form split Reduction surjective iff sup eq top
-- statement:
--   Exact algebraic form of the remaining construction-specialized strong
--   approximation statement.  Because split local lifting is already proved,
--   restriction to the genuine cyclic-order descent subgroup is onto precisely
--   when that subgroup together with the split congruence kernel fills the whole
--   split integral special-linear group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L894-L931
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L894-L931

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerForm_splitReduction_surjective_iff_sup_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
        ((orderSpecialLinearReduction P r level).comp
          (OrderNormOneInnerForm P r).subtype) ↔
      OrderNormOneInnerForm P r ⊔
          OrderSpecialLinearCongruenceSubgroup P r level = ⊤ := by sorry
