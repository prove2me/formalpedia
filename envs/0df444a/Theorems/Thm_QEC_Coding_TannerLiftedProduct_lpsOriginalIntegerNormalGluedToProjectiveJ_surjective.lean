-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:04:43.421646+00:00
-- url     : https://prove2.me/theorems/f9c272be-429a-459e-b80d-e889a61bc3e7
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued To Projective J surjective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued To Projective J surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L115-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L115-L130

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_surjective
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalGluedToProjectiveJ N hN) := by sorry
