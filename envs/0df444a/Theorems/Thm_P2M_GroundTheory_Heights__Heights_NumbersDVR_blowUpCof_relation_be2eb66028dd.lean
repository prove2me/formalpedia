-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_relation_be2eb66028dd
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_relation_be2eb66028dd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:23.031016+00:00
-- url     : https://prove2.me/theorems/eac970c8-42fc-43dd-96a3-7d488cf149bd
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR blow Up Cof relation be2eb66028dd: P2 M Ground Theory Heights  Heights Numbers DVR blow Up Cof relation be2eb66028dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR blow Up Cof relation be2eb66028dd construction uses the P2 M Ground Theory Heights  Heights Numbers DVR blow Up Cof relation be2eb66028dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L125-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L125-L139

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_relation_be2eb66028dd {P : Ideal (MRing ι R)} (hP : P.IsPrime) {s g f m u₀ v₀ : MRing ι R}
    (e : K → ℕ) (hg : g ∉ P) (h : u₀ * f - v₀ * g ∈ P) (j j' : BlowUpIdx ι) :
    newVar j * liftForm (blowUpCof s m e u₀ v₀ j') - newVar j' * liftForm (blowUpCof s m e u₀ v₀ j) ∈
      blowUpOf P (blowUpGens s g f m e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«blowUpCof_relation» := P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_relation_be2eb66028dd
