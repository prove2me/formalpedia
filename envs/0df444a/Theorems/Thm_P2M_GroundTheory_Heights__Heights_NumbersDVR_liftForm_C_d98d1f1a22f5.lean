-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_d98d1f1a22f5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_d98d1f1a22f5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:02.293815+00:00
-- url     : https://prove2.me/theorems/376048af-31fe-4717-a6a1-c3be42c73529
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lift Form C d98d1f1a22f5: P2 M Ground Theory Heights  Heights Numbers DVR lift Form C d98d1f1a22f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lift Form C d98d1f1a22f5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lift Form C d98d1f1a22f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L51-L52

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_d98d1f1a22f5 {J : Type} (r : R) : liftForm (J := J) (C r : MRing ι R) = C r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«liftForm_C» := P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_d98d1f1a22f5
