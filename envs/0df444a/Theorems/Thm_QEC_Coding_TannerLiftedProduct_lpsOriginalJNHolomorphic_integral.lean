-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNHolomorphic_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNHolomorphic_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:15:45.949187+00:00
-- url     : https://prove2.me/theorems/fd063ca9-12eb-41f5-833a-c4ad81e80a15
-- title:
--   Tanner Lifted Product: lps Original JNHolomorphic integral
-- statement:
--   Actual original jN is integral over the image of C[j], using the proved monic original relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L86-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L86-L107

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNHolomorphic_integral (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalJHolomorphicEval.toRingHom.IsIntegralElem
      (lpsOriginalJNHolomorphic N hN) := by sorry
