-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_spec_933dc8cb6ebe
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_spec_933dc8cb6ebe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:53.738995+00:00
-- url     : https://prove2.me/theorems/a2c743ef-0794-45b8-abed-b050ccf23775
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR blow Up Cof spec 933dc8cb6ebe: P2 M Ground Theory Heights  Heights Numbers DVR blow Up Cof spec 933dc8cb6ebe
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR blow Up Cof spec 933dc8cb6ebe construction uses the P2 M Ground Theory Heights  Heights Numbers DVR blow Up Cof spec 933dc8cb6ebe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L110-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L110-L123

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_spec_933dc8cb6ebe {P : Ideal (MRing ι R)} {s g f m u₀ v₀ : MRing ι R} (e : K → ℕ)
    (h : u₀ * f - v₀ * g ∈ P) (j : BlowUpIdx ι) :
    u₀ * blowUpGens s g f m e j - g * blowUpCof s m e u₀ v₀ j ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«blowUpCof_spec» := P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_spec_933dc8cb6ebe
