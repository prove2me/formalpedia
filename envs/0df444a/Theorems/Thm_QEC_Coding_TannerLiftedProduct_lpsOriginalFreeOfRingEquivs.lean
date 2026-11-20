-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFreeOfRingEquivs
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFreeOfRingEquivs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:54:02.134713+00:00
-- url     : https://prove2.me/theorems/ef94d2ee-2658-40f7-a7c2-11d6af87915c
-- title:
--   Tanner Lifted Product: lps Original Free Of Ring Equivs
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Free Of Ring Equivs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointInteger.lean#L171-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointInteger.lean#L171-L186

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFreeOfRingEquivs
    {A₁ B₁ A₂ B₂ : Type*} [CommSemiring A₁] [CommSemiring B₁]
    [CommSemiring A₂] [CommSemiring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂]
    (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap A₁ B₁))
    [Module.Free A₁ B₁] : Module.Free A₂ B₂ := by sorry
