-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticCharacter_fourier
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticCharacter_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:00.414389+00:00
-- url     : https://prove2.me/theorems/4611876f-e36e-4dec-a044-3a784425412c
-- title:
--   Tanner Lifted Product: lps Quadratic Character fourier
-- statement:
--   The actual nontrivial quadratic character has its genuine finite Fourier transform.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L26-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean#L26-L38

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticCharacter_fourier (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ≠1) (hχq : χ.IsQuadratic) (ψ : AddChar F ℂ) (a : F) :
    (∑ r : F, χ r*ψ (a*r))=χ a*gaussSum χ ψ := by sorry
