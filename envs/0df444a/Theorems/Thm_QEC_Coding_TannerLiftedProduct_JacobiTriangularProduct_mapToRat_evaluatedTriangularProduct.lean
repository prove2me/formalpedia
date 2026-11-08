-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_mapToRat_evaluatedTriangularProduct
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.mapToRat_evaluatedTriangularProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:35:33.949253+00:00
-- url     : https://prove2.me/theorems/5f8a5665-089f-447a-bb15-c5bbb12e6eb6
-- title:
--   Jacobi Triangular Product: map To Rat evaluated Triangular Product
-- statement:
--   The Jacobi Triangular Product construction uses the map To Rat evaluated Triangular Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTriangularProduct.lean#L556-L566
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTriangularProduct.lean#L556-L566

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

theorem QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.mapToRat_evaluatedTriangularProduct :
    mapToRat evaluatedTriangularProduct = jacobiTriangularProduct := by sorry
