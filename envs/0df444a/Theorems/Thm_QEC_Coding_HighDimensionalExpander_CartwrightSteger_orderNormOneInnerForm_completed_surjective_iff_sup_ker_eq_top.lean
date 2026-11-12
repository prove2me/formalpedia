-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerForm_completed_surjective_iff_sup_ker_eq_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerForm_completed_surjective_iff_sup_ker_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:13:13.007761+00:00
-- url     : https://prove2.me/theorems/94625fa6-0555-427f-ab0c-cea8f879f1d6
-- title:
--   Cartwright Steger: order Norm One Inner Form completed surjective iff sup ker eq top
-- statement:
--   Exact remaining global approximation criterion: since completed local
--   norm-one reduction is already onto, global norm-one reduction is onto iff
--   the global completed image together with the local congruence kernel fills
--   the completed norm-one group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3386-L3427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3386-L3427

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerForm_completed_surjective_iff_sup_ker_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
        ((indexCompletedNormOneReduction P r level).comp
          (orderNormOneInnerFormToCompleted P r level)) ↔
      (orderNormOneInnerFormToCompleted P r level).range ⊔
        (indexCompletedNormOneReduction P r level).ker = ⊤ := by sorry
