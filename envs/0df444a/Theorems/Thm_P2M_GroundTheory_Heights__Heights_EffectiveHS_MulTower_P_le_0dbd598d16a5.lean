-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_P_le_0dbd598d16a5
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_P_le_0dbd598d16a5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:14.671031+00:00
-- url     : https://prove2.me/theorems/d1e3b0a2-04cb-438f-ab7f-22e64c51f037
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower P le 0dbd598d16a5: P2 M Ground Theory Heights  Heights Effective HS Mul Tower P le 0dbd598d16a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower P le 0dbd598d16a5 construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower P le 0dbd598d16a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L91-L95

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_P_le_0dbd598d16a5 (hs : ∀ i, s i ∈ τ.W) {T : ℕ} (hDT : D ≤ T) : τ.P D T s ≤ τ.V T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«P_le» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_P_le_0dbd598d16a5
