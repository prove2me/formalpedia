-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_liftVar_injective_d44a11af5a3d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_liftVar_injective_d44a11af5a3d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:35.714801+00:00
-- url     : https://prove2.me/theorems/1520be1d-6c3f-4b87-97c4-4fab59ede739
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Variety lift Var injective d44a11af5a3d: P2 M Ground Theory Heights  Heights Numbers DVR Join Variety lift Var injective d44a11af5a3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Variety lift Var injective d44a11af5a3d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Variety lift Var injective d44a11af5a3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinVariety.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinVariety.lean#L33-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinVariety
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinVariety
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVariety
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_liftVar_injective_d44a11af5a3d : Function.Injective (liftVar (ι := ι) ptIdx) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVariety».«liftVar_injective» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_liftVar_injective_d44a11af5a3d
