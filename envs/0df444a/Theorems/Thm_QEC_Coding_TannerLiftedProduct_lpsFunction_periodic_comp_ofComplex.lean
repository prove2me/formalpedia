-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFunction_periodic_comp_ofComplex
-- name    : QEC.Coding.TannerLiftedProduct.lpsFunction_periodic_comp_ofComplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:17.513008+00:00
-- url     : https://prove2.me/theorems/9b4109a6-fc76-4f3c-8680-54aafa7d0ee7
-- title:
--   Tanner Lifted Product: lps Function periodic comp of Complex
-- statement:
--   Actual translation periodicity extends through the upper-half-plane retraction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L216-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L216-L231

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsFunction_periodic_comp_ofComplex (f : ℍ→ℂ)
    (hf : ∀ z, f ((1:ℝ) +ᵥ z)=f z) : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1 := by sorry
