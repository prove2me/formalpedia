-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_Vpp_c93286f36977
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_Vpp_c93286f36977
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:36.522899+00:00
-- url     : https://prove2.me/theorems/cecbf684-5108-4886-b6ea-511af6163a71
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower gen mem Vpp c93286f36977: P2 M Ground Theory Heights  Heights Effective HS Mul Tower gen mem Vpp c93286f36977
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower gen mem Vpp c93286f36977 construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower gen mem Vpp c93286f36977 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L86-L89

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_Vpp_c93286f36977 {T a₀ : ℕ} (α : Fin D → ℕ) {k : ℕ} (w : Fin k → A)
    (hw : ∀ i, w i ∈ τ.W) {m : A} (hm : m ∈ τ.V 0) (hT : ∑ i, α i + k = T)
    (ha : ∑ i, α i ≤ a₀) : mono s α * (∏ i, w i) * m ∈ τ.Vpp D T a₀ s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«gen_mem_Vpp» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_Vpp_c93286f36977
