-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalSubfield_eval__mem_0d401beef6d5
-- name    : P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalSubfield_eval__mem_0d401beef6d5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:24:31.306699+00:00
-- url     : https://prove2.me/theorems/f10a0648-60e3-42fa-835a-1280772141c4
-- title:
--   P2 M QEC Coding Tanner Lifted Product lps Original Subfield eval  mem 0d401beef6d5: P2 M QEC Coding Tanner Lifted Product lps Original Subfield eval  mem 0d401beef6d5
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product lps Original Subfield eval  mem 0d401beef6d5 construction uses the P2 M QEC Coding Tanner Lifted Product lps Original Subfield eval  mem 0d401beef6d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L281-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L281-L291

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalSubfield_eval__mem_0d401beef6d5
    (R K : Type*) [CommRing R] [Field K] (f : R →+* K)
    (S : Subfield K) (hf : ∀ a, f a ∈ S) (x : K) (hx : x ∈ S)
    (P : Polynomial R) : P.eval₂ f x ∈ S := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«lpsOriginalSubfield_eval₂_mem» := P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalSubfield_eval__mem_0d401beef6d5
