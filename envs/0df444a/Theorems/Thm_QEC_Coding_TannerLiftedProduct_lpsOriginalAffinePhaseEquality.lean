-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffinePhaseEquality
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAffinePhaseEquality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:16:58.233183+00:00
-- url     : https://prove2.me/theorems/3ade02b7-23d7-4688-8765-b2defd8325f1
-- title:
--   Tanner Lifted Product: lps Original Affine Phase Equality
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Affine Phase Equality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L168-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L168-L179

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAffinePhaseEquality (m : ℕ) (hm : 0 < m)
    (r s : ℝ)
    (he : Function.Periodic.qParam 1 (r : ℂ) = Function.Periodic.qParam 1 (s : ℂ))
    (τ : ℍ) :
    lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ) =
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm s • τ) := by sorry
