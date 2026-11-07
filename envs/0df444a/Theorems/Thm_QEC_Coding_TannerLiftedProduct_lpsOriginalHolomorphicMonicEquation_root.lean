-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicMonicEquation_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicMonicEquation_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:38:27.684797+00:00
-- url     : https://prove2.me/theorems/d95c9807-bc8b-4cc7-8d93-96e86440f54b
-- title:
--   Tanner Lifted Product: lps Original Holomorphic Monic Equation root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Holomorphic Monic Equation root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L112-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L112-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicMonicEquation_root (N : ℕ) [NeZero N] (k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) (f : ℍ → ℂ)
    (hf : ∀ τ, A τ = ModularForm.discriminant τ^k * f τ) (τ : ℍ) :
    (lpsOriginalHolomorphicMonicEquation N k A).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (f τ) = 0 := by sorry
