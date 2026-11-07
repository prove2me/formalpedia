-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_holomorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_holomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:01:21.335893+00:00
-- url     : https://prove2.me/theorems/62cd2f97-0d98-404f-8879-2067f942c68b
-- title:
--   Tanner Lifted Product: lps Original Filled JReciprocal holomorphic
-- statement:
--   Global reciprocal holomorphy on the same original filled manifold from actual chart analyticity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L179-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L179-L193

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_holomorphic (N : ℕ) [NeZero N] (hN : 4∣N)
    (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalFilledJReciprocal N a) := by sorry
