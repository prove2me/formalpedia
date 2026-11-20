-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRingHom_prod_ker
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRingHom_prod_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:51:58.126692+00:00
-- url     : https://prove2.me/theorems/cb35d883-0359-4741-8f20-f140193baf9f
-- title:
--   Tanner Lifted Product: lps Original Ring Hom prod ker
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Ring Hom prod ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L224-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L224-L229

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRingHom_prod_ker
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) :
    RingHom.ker (f.prod g) = RingHom.ker f ⊓ RingHom.ker g := by sorry
