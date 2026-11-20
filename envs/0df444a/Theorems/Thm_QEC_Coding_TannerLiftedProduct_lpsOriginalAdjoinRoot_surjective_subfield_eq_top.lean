-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRoot_surjective_subfield_eq_top
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRoot_surjective_subfield_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:26:45.998088+00:00
-- url     : https://prove2.me/theorems/f7c48fa6-a6fb-4035-a6c5-4470d7c4c773
-- title:
--   Tanner Lifted Product: lps Original Adjoin Root surjective subfield eq top
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Adjoin Root surjective subfield eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L307-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L307-L318

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRoot_surjective_subfield_eq_top
    (R K : Type*) [CommRing R] [Field K] (P : Polynomial R)
    (f : AdjoinRoot P →+* K) (hf : Function.Surjective f)
    (S : Subfield K) (hc : ∀ a : R, f (AdjoinRoot.of P a) ∈ S)
    (hx : f (AdjoinRoot.root P) ∈ S) : S = ⊤ := by sorry
