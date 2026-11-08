-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_evalOuter_hasSum_choose_nonnegative
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.evalOuter_hasSum_choose_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:34:12.211283+00:00
-- url     : https://prove2.me/theorems/65083034-deb3-45f9-8f70-131c0efe9555
-- title:
--   Jacobi Triangular Product: eval Outer has Sum choose nonnegative
-- statement:
--   The Jacobi Triangular Product construction uses the eval Outer has Sum choose nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTriangularProduct.lean#L155-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTriangularProduct.lean#L155-L164

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

theorem QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.evalOuter_hasSum_choose_nonnegative (k : ℕ) :
    HasSum (evalOuter ∘ fun m : ℕ =>
      ((PowerSeries.X : Outer) ^ (m + k).choose 2 *
        qPochhammerInf (PowerSeries.X * PowerSeries.X ^ (m + k)) *
        (PowerSeries.X ^ m.choose 2 * PowerSeries.X ^ m *
          qPochhammerInv (R := DiscreteTarget) m)))
      (((PowerSeries.X : Target) ^ 2) ^ k.choose 2) := by sorry
