-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJointTensorMap_surjective_of_jointClosure
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJointTensorMap_surjective_of_jointClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:52:34.669628+00:00
-- url     : https://prove2.me/theorems/31612320-cee0-46c8-a04a-f16e6a2987dc
-- title:
--   Tanner Lifted Product: lps Original Joint Tensor Map surjective of joint Closure
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Joint Tensor Map surjective of joint Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L128-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L128-L143

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJointTensorMap_surjective_of_jointClosure
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Subring.closure (Set.range f ∪ Set.range g) = ⊤) :
    Function.Surjective (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)) := by sorry
