-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiGeometricSeries_subst_mul_one_sub
-- name    : QEC.Coding.TannerLiftedProduct.jacobiGeometricSeries_subst_mul_one_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:34.4789+00:00
-- url     : https://prove2.me/theorems/1f94a196-4e9b-4c90-b7eb-04917c4c9690
-- title:
--   Tanner Lifted Product: jacobi Geometric Series subst mul one sub
-- statement:
--   Substitution in the geometric series produces the inverse of `1 - a`
--   whenever substitution at `a` is defined.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L27-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L27-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobiGeometricSeries_subst_mul_one_sub
    {a : ℚ⟦X⟧} (hs : PowerSeries.HasSubst a) :
    (jacobiGeometricSeries.subst a) * (1 - a) = 1 := by sorry
