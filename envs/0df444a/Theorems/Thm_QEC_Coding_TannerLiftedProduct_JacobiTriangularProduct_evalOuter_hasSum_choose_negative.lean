-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_evalOuter_hasSum_choose_negative
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.evalOuter_hasSum_choose_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:33:37.151351+00:00
-- url     : https://prove2.me/theorems/641235da-602c-4dfb-93d8-08deb4a11497
-- title:
--   Jacobi Triangular Product: eval Outer has Sum choose negative
-- statement:
--   The Jacobi Triangular Product construction uses the eval Outer has Sum choose negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTriangularProduct.lean#L166-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTriangularProduct.lean#L166-L176

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.WithTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
open JacobiGeneralCore.FormalPowerSeries
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatUniformSpace
attribute [local instance] discreteRatUniformSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatTopologicalSpace
attribute [local instance] discreteRatTopologicalSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatUniformity
attribute [local instance] discreteRatUniformity
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatTopology
attribute [local instance] discreteRatTopology
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetUniformSpace
attribute [local instance] discreteTargetUniformSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetTopologicalSpace
attribute [local instance] discreteTargetTopologicalSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetUniformity
attribute [local instance] discreteTargetUniformity
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetTopology
attribute [local instance] discreteTargetTopology

theorem QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.evalOuter_hasSum_choose_negative (l : ℕ) :
    HasSum (evalOuter ∘ fun n : ℕ =>
      ((PowerSeries.X : Outer) ^ n.choose 2 *
        qPochhammerInf (PowerSeries.X * PowerSeries.X ^ n) *
        (PowerSeries.X ^ (n + (l + 1)).choose 2 *
          PowerSeries.X ^ (n + (l + 1)) *
          qPochhammerInv (R := DiscreteTarget) (n + (l + 1)))))
      (((PowerSeries.X : Target) ^ 2) ^ (l + 2).choose 2) := by sorry
