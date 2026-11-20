-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLocalization_subfield_mem
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLocalization_subfield_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:25:55.492511+00:00
-- url     : https://prove2.me/theorems/bc414bbb-f484-48f4-91a1-ae731efab3a5
-- title:
--   Tanner Lifted Product: lps Original Localization subfield mem
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Localization subfield mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L293-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L293-L305

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLocalization_subfield_mem
    (R A K : Type*) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] (M : Submonoid R) [IsLocalization M A]
    (f : A →+* K) (S : Subfield K)
    (hf : ∀ a : R, f (algebraMap R A a) ∈ S) (x : A) : f x ∈ S := by sorry
