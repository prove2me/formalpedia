-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:42.590284+00:00
-- url     : https://prove2.me/theorems/5005f9e8-f749-413a-a8f7-08a117f673b3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR aeval blow Up Subst lift Form 4b99591f2332: P2 M Ground Theory Heights  Heights Numbers DVR aeval blow Up Subst lift Form 4b99591f2332
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR aeval blow Up Subst lift Form 4b99591f2332 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR aeval blow Up Subst lift Form 4b99591f2332 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L286-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L286-L294

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332 {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) (u : J → MRing ι R) (p : MRing ι R) :
    aeval (blowUpSubst P u) (liftForm p) = Polynomial.C (Ideal.Quotient.mk P p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«aeval_blowUpSubst_liftForm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332
