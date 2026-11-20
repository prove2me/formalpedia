-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionLift_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFractionLift_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:26:32.07626+00:00
-- url     : https://prove2.me/theorems/870c5dae-0799-45ab-bc30-c2f23f911763
-- title:
--   Tanner Lifted Product: lps Original Fraction Lift polynomial
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Fraction Lift polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L193-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L193-L200

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFractionLift_polynomial
    (F K : Type*) [Field F] [Field K]
    (f : Polynomial F →+* K) (hf : Function.Injective f) :
    (IsFractionRing.lift (K := FractionRing (Polynomial F)) hf).comp
      (algebraMap (Polynomial F) (FractionRing (Polynomial F))) = f := by sorry
