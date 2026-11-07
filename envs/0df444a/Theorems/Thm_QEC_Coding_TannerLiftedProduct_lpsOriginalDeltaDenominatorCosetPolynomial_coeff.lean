-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDenominatorCosetPolynomial_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDenominatorCosetPolynomial_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:38:31.846201+00:00
-- url     : https://prove2.me/theorems/b18692fe-faae-4d94-b53b-9842a9c7d237
-- title:
--   Tanner Lifted Product: lps Original Delta Denominator Coset Polynomial coeff
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Delta Denominator Coset Polynomial coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L37-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L37-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDenominatorCosetPolynomial_coeff
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A
      (lpsOriginalMeromorphicDeltaPowerAtLevel N k) τ).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        (-1 : ℂ)^(Nat.card (LPSOriginalMeromorphicCosets N)) *
          ModularForm.discriminant τ^(k * Nat.card (LPSOriginalMeromorphicCosets N)) := by sorry
