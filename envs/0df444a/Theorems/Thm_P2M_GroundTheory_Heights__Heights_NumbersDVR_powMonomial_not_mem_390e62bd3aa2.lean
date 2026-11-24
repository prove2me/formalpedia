-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_not_mem_390e62bd3aa2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_not_mem_390e62bd3aa2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:00.535403+00:00
-- url     : https://prove2.me/theorems/f7a8ea54-e318-48de-909d-3dcf757e99b8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR pow Monomial not mem 390e62bd3aa2: P2 M Ground Theory Heights  Heights Numbers DVR pow Monomial not mem 390e62bd3aa2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR pow Monomial not mem 390e62bd3aa2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR pow Monomial not mem 390e62bd3aa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L97-L103

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_not_mem_390e62bd3aa2 {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hrel : IsRelevant W) (e : K → ℕ) :
    ∃ i : ∀ k, ι k, powMonomial e i ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«powMonomial_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_not_mem_390e62bd3aa2
