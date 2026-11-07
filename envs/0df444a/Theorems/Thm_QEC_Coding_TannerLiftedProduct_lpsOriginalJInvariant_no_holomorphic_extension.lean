-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_no_holomorphic_extension
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_no_holomorphic_extension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:25:00.452738+00:00
-- url     : https://prove2.me/theorems/64102f2d-0813-4340-9d31-b0e1e29b187d
-- title:
--   Tanner Lifted Product: lps Original JInvariant no holomorphic extension
-- statement:
--   The same nonconstant j admits no global holomorphic extension on the actual compact connected curve; uses connectedness/constant-field proof, not assumed extension failure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L288-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L288-L299

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_no_holomorphic_extension (N : ℕ) [NeZero N] (hN : 4∣N) :
    ¬∃ f : LPSOriginalFilledCurve N→ℂ,
      (letI := lpsOriginalFilledTopology N;
        letI := lpsOriginalFilledChartedSpace N hN;
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) ∧
      (∀ τ : ℍ, f (Sum.inl ⟦τ⟧)=lpsOriginalJInvariant τ) := by sorry
