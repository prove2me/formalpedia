-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Vpp_le_ae2dcd98d56b
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Vpp_le_ae2dcd98d56b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:00.639166+00:00
-- url     : https://prove2.me/theorems/7b96ac7b-3844-5261-b508-3beaf14c2e68
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower Vpp le ae2dcd98d56b: P2 M Ground Theory Heights  Heights Effective HS Mul Tower Vpp le ae2dcd98d56b
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower Vpp le ae2dcd98d56b construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower Vpp le ae2dcd98d56b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L97-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)
variable {D : ℕ} {s : Fin D → A}

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Vpp_le_ae2dcd98d56b (hs : ∀ i, s i ∈ τ.W) {T a₀ : ℕ} (hDT : D ≤ T) : τ.Vpp D T a₀ s ≤ τ.V T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«Vpp_le» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Vpp_le_ae2dcd98d56b
