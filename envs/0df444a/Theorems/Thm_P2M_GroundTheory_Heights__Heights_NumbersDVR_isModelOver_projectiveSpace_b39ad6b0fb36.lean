-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isModelOver_projectiveSpace_b39ad6b0fb36
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isModelOver_projectiveSpace_b39ad6b0fb36
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:05.406854+00:00
-- url     : https://prove2.me/theorems/a4b692d7-18bc-48a7-a62e-67ac0142408e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Model Over projective Space b39ad6b0fb36: P2 M Ground Theory Heights  Heights Numbers DVR is Model Over projective Space b39ad6b0fb36
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Model Over projective Space b39ad6b0fb36 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Model Over projective Space b39ad6b0fb36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Objects.lean#L175-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Objects.lean#L175-L190

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isModelOver_projectiveSpace_b39ad6b0fb36 {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (n : ℕ) :
    IsModelOver (⊥ : Ideal (MRing (fun _ : Unit => Fin (n + 1)) O)) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isModelOver_projectiveSpace» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isModelOver_projectiveSpace_b39ad6b0fb36
