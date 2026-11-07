-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToSpecZ_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:31.915055+00:00
-- url     : https://prove2.me/theorems/90f6de9b-b687-4280-88e8-359c9cd12c5f
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued To Spec Z surjective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued To Spec Z surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L144-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L144-L151

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToSpecZ_surjective
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalGluedToSpecZ N hN) := by sorry
