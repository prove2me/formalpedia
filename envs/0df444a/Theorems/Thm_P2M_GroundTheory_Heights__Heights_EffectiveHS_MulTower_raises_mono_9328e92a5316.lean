-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_mono_9328e92a5316
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_mono_9328e92a5316
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:52.796261+00:00
-- url     : https://prove2.me/theorems/1fd1d3f1-248f-4157-b368-67165f77d5fa
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises mono 9328e92a5316: P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises mono 9328e92a5316
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises mono 9328e92a5316 construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises mono 9328e92a5316 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L59-L63

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_mono_9328e92a5316 {D : ℕ} {s : Fin D → A} (hs : ∀ i, s i ∈ τ.W) (α : Fin D → ℕ) :
    τ.Raises (∑ i, α i) (mono s α) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«raises_mono» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_mono_9328e92a5316
