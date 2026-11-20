-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSurjectiveProductKernels_coprime
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSurjectiveProductKernels_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:27.2705+00:00
-- url     : https://prove2.me/theorems/a3a0a67c-c2fe-4fa1-bd39-415aa928b4f9
-- title:
--   Tanner Lifted Product: lps Original Surjective Product Kernels coprime
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Surjective Product Kernels coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L266-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L266-L276

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSurjectiveProductKernels_coprime
    {R K L : Type*} [CommRing R] [CommRing K] [CommRing L]
    (f : R →+* K × L) (hf : Function.Surjective f) :
    IsCoprime (RingHom.ker ((RingHom.fst K L).comp f))
      (RingHom.ker ((RingHom.snd K L).comp f)) := by sorry
