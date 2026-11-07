-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionFieldEquiv_fieldPoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFractionFieldEquiv_fieldPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:12:27.582409+00:00
-- url     : https://prove2.me/theorems/5da5a511-2438-4efc-830d-e23c093c1ad8
-- title:
--   Tanner Lifted Product: lps Original Fraction Field Equiv field Point
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Fraction Field Equiv field Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L206-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L206-L222

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFractionFieldEquiv_fieldPoint (R : CommRingCat.{u}) [IsDomain R]
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] :
    Spec.map (CommRingCat.ofHom (IsFractionRing.ringEquivOfRingEquiv
      (K := (Spec R).functionField) (L := F) (RingEquiv.refl R)).toRingHom) ≫
        (Spec R).fromSpecStalk (genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R F)) := by sorry
