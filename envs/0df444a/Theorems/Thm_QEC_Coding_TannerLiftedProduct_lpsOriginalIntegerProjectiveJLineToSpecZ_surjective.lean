-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLineToSpecZ_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLineToSpecZ_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:04:34.093881+00:00
-- url     : https://prove2.me/theorems/d78af346-1ee0-4ccd-8df1-9c34d46ea299
-- title:
--   Tanner Lifted Product: lps Original Integer Projective JLine To Spec Z surjective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective JLine To Spec Z surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L132-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerFlatModel.lean#L132-L142

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLineToSpecZ_surjective :
    Surjective lpsOriginalIntegerProjectiveJLineToSpecZ := by sorry
