-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_300a56edc436
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_300a56edc436
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:40.701808+00:00
-- url     : https://prove2.me/theorems/6c1facec-89b4-5dd7-9d3a-98589242906d
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower gen mem 300a56edc436: P2 M Ground Theory Heights  Heights Effective HS Mul Tower gen mem 300a56edc436
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower gen mem 300a56edc436 construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower gen mem 300a56edc436 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L80-L84

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_300a56edc436 (hs : ∀ i, s i ∈ τ.W) {T : ℕ} (α : Fin D → ℕ) {k : ℕ} (w : Fin k → A)
    (hw : ∀ i, w i ∈ τ.W) {m : A} (hm : m ∈ τ.V 0) (hT : ∑ i, α i + k = T) :
    mono s α * (∏ i, w i) * m ∈ τ.V T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«gen_mem» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_300a56edc436
