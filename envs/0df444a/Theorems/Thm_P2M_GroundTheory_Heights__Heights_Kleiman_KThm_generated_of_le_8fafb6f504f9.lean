-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_of_le_8fafb6f504f9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_of_le_8fafb6f504f9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:09:00.495802+00:00
-- url     : https://prove2.me/theorems/e4385c6f-17ac-4600-9543-ace3c8ea2805
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm generated of le 8fafb6f504f9: P2 M Ground Theory Heights  Heights Kleiman KThm generated of le 8fafb6f504f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm generated of le 8fafb6f504f9 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm generated of le 8fafb6f504f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L69-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_of_le_8fafb6f504f9 (F : SubSystem S x Ω)
    (h : ∀ I, F.sub I ≤ Submodule.span (chartRing S x I) (F.secs : Set Ω)) : F.Generated := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«generated_of_le» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_of_le_8fafb6f504f9
