-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_blowUpOf_82c52e9c4e5f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_blowUpOf_82c52e9c4e5f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:27.066262+00:00
-- url     : https://prove2.me/theorems/d764e2e3-40cf-4671-bff2-883d357f3c94
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal blow Up Of 82c52e9c4e5f: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal blow Up Of 82c52e9c4e5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal blow Up Of 82c52e9c4e5f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal blow Up Of 82c52e9c4e5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L97-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L97-L176

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
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
variable {K : Type*} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_blowUpOf_82c52e9c4e5f {P : Ideal (MRing ι R)} (hP : IsMultiHomogIdeal P) (N : K → ℕ)
    (u : J → MRing ι R) (hu : ∀ j, IsMultiHomog (u j) N) : IsMultiHomogIdeal (blowUpOf P u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiHomogIdeal_blowUpOf» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_blowUpOf_82c52e9c4e5f
