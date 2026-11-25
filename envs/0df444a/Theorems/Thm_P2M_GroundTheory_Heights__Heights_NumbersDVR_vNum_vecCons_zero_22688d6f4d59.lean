-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_vecCons_zero_22688d6f4d59
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_vecCons_zero_22688d6f4d59
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:12:58.657796+00:00
-- url     : https://prove2.me/theorems/ac75afe6-44ad-4c29-8abc-0cd7f322498b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR v Num vec Cons zero 22688d6f4d59: P2 M Ground Theory Heights  Heights Numbers DVR v Num vec Cons zero 22688d6f4d59
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR v Num vec Cons zero 22688d6f4d59 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR v Num vec Cons zero 22688d6f4d59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalEqAddMulOfCycle.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalEqAddMulOfCycle.lean#L53-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalEqAddMulOfCycle
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_vecCons_zero_22688d6f4d59 (W : Ideal (MRing ι O)) {d : ℕ} (L : Fin d → K → ℤ) :
    vNum W (Matrix.vecCons (0 : K → ℤ) L) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«vNum_vecCons_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_vecCons_zero_22688d6f4d59
