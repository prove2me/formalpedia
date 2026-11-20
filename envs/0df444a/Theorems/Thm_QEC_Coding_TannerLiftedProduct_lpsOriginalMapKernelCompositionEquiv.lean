-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMapKernelCompositionEquiv
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMapKernelCompositionEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:58:24.844173+00:00
-- url     : https://prove2.me/theorems/d7d1561a-a318-45c2-abb9-2ffb7ecd868a
-- title:
--   Tanner Lifted Product: lps Original Map Kernel Composition Equiv
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Map Kernel Composition Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L88-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L88-L96

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMapKernelCompositionEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (e : R ≃+* A) (f : A →+* B) :
    (RingHom.ker (f.comp e.toRingHom)).map e = RingHom.ker f := by sorry
