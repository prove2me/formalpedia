-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRestrictedDelta_coset
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRestrictedDelta_coset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:39:06.10119+00:00
-- url     : https://prove2.me/theorems/85dabea2-e346-48a5-ab5f-c27653cd9a0d
-- title:
--   Tanner Lifted Product: lps Original Restricted Delta coset
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Restricted Delta coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L25-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L25-L35

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRestrictedDelta_coset (N : ℕ) (k : ℕ)
    (q : LPSOriginalMeromorphicCosets N) (τ : ℍ) :
    SlashInvariantForm.quotientFunc (lpsOriginalMeromorphicDeltaPowerAtLevel N k) q τ =
      ModularForm.discriminant τ ^ k := by sorry
