-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSurjectiveProductKernels_product
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSurjectiveProductKernels_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:27:10.968171+00:00
-- url     : https://prove2.me/theorems/8fdad666-6eab-45b2-84c3-1a787a903782
-- title:
--   Tanner Lifted Product: lps Original Surjective Product Kernels product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Surjective Product Kernels product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L278-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L278-L285

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSurjectiveProductKernels_product
    {R K L : Type*} [CommRing R] [CommRing K] [CommRing L]
    (f : R →+* K × L) (hf : Function.Surjective f) :
    (RingHom.ker ((RingHom.fst K L).comp f)) *
      (RingHom.ker ((RingHom.snd K L).comp f)) = RingHom.ker f := by sorry
