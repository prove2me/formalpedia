-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_X_709b97b21fde
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_X_709b97b21fde
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:37.660127+00:00
-- url     : https://prove2.me/theorems/16b3f52e-0cdf-4382-928e-74723f3ae611
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lift Form X 709b97b21fde: P2 M Ground Theory Heights  Heights Numbers DVR lift Form X 709b97b21fde
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lift Form X 709b97b21fde construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lift Form X 709b97b21fde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L47-L49

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_X_709b97b21fde {J : Type} (v : Σ k, ι k) :
    liftForm (J := J) (X v : MRing ι R) = X ⟨some v.1, v.2⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«liftForm_X» := P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_X_709b97b21fde
