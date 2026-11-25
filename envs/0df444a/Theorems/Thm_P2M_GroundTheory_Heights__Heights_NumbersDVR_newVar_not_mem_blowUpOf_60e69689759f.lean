-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_newVar_not_mem_blowUpOf_60e69689759f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_newVar_not_mem_blowUpOf_60e69689759f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:12:39.206332+00:00
-- url     : https://prove2.me/theorems/7432b87c-1667-489c-9462-6d189db085a9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR new Var not mem blow Up Of 60e69689759f: P2 M Ground Theory Heights  Heights Numbers DVR new Var not mem blow Up Of 60e69689759f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR new Var not mem blow Up Of 60e69689759f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR new Var not mem blow Up Of 60e69689759f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L67-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
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
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
variable {J : Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_newVar_not_mem_blowUpOf_60e69689759f {P : Ideal (MRing ι R)} {u : J → MRing ι R} {j : J} (h : u j ∉ P) :
    (newVar j : MRing (extIdx ι J) R) ∉ blowUpOf P u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«newVar_not_mem_blowUpOf» := P2M_GroundTheory_Heights__Heights_NumbersDVR_newVar_not_mem_blowUpOf_60e69689759f
