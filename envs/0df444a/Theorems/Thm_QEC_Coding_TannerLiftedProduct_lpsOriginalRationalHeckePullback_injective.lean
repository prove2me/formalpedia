-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalHeckePullback_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T03:52:58.303845+00:00
-- url     : https://prove2.me/theorems/275198d0-6f3b-4127-95be-6f905804af81
-- title:
--   Tanner Lifted Product: lps Original Rational Hecke Pullback injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rational Hecke Pullback injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L408-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L408-L411

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_injective (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    Function.Injective (lpsOriginalRationalHeckePullback N p hN hp h4N) := by sorry
