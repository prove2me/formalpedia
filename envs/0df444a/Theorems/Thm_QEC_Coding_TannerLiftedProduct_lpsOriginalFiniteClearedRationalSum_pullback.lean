-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedRationalSum_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:15:25.923438+00:00
-- url     : https://prove2.me/theorems/5b691f37-498d-4b08-b19c-4335d6168ed0
-- title:
--   Tanner Lifted Product: lps Original Finite Cleared Rational Sum pullback
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Finite Cleared Rational Sum pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L335-L349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L335-L349

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedRationalSum_pullback
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℚ)
    (hB : ∀ i, u i + M * v i ≤ B) (τ : ℍ) :
    lpsOriginalFiniteClearedRationalSum M B u v a
        (Function.Periodic.qParam 1 (τ : ℂ)) =
      (Function.Periodic.qParam 1 (τ : ℂ)) ^ B *
        (lpsOriginalRationalMonomialHolomorphicSum M hM u v a).val τ := by sorry
