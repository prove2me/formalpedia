-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_alt_b932b45f2d8a
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_alt_b932b45f2d8a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:19.546569+00:00
-- url     : https://prove2.me/theorems/d34aa2a9-6188-5f17-a1fa-25b1dcd1eb34
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises prod alt b932b45f2d8a: P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises prod alt b932b45f2d8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises prod alt b932b45f2d8a construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises prod alt b932b45f2d8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L65-L68

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_alt_b932b45f2d8a {k : ℕ} (w : Fin k → A) (hw : ∀ i, w i ∈ τ.W) :
    τ.Raises k (∏ i, w i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«raises_prod_alt» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_alt_b932b45f2d8a
