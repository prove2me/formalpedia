-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_liftForm_b9c03287c289
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_liftForm_b9c03287c289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:33.587056+00:00
-- url     : https://prove2.me/theorems/b90d7de6-dd3a-4761-976d-d571e3f73b87
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR aeval chart Subst lift Form b9c03287c289: P2 M Ground Theory Heights  Heights Numbers DVR aeval chart Subst lift Form b9c03287c289
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR aeval chart Subst lift Form b9c03287c289 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR aeval chart Subst lift Form b9c03287c289 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalChartSubstMemOfMemBlowUpOf.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalChartSubstMemOfMemBlowUpOf.lean#L22-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalChartSubstMemOfMemBlowUpOf
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
universe u
noncomputable section
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_liftForm_b9c03287c289 (a : J → MRing ι R) (p : MRing ι R) :
    aeval (chartSubst a) (liftForm p) = Polynomial.C p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«aeval_chartSubst_liftForm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_liftForm_b9c03287c289
