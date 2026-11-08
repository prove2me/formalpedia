-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_jacobiTriangularProduct_eq_rationalTriangularThetaSeries
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.jacobiTriangularProduct_eq_rationalTriangularThetaSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:36:22.144108+00:00
-- url     : https://prove2.me/theorems/ae5f3eee-3ecb-4bd5-bc11-2deb396afd27
-- title:
--   Jacobi Triangular Product: jacobi Triangular Product eq rational Triangular Theta Series
-- statement:
--   Jacobi's triangular-number product identity over rational formal power
--   series, obtained by a legal nested-FPS specialization of the fixed-base
--   triple-product proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTriangularProduct.lean#L740-L751
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTriangularProduct.lean#L740-L751

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

theorem QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.jacobiTriangularProduct_eq_rationalTriangularThetaSeries :
    jacobiTriangularProduct = rationalTriangularThetaSeries := by sorry
