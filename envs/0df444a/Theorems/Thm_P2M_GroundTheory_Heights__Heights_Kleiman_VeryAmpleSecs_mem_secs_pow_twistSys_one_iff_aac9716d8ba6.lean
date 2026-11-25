-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_secs_pow_twistSys_one_iff_aac9716d8ba6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_secs_pow_twistSys_one_iff_aac9716d8ba6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:59:20.769228+00:00
-- url     : https://prove2.me/theorems/559378cf-8676-497f-b1f7-23aafdae19b8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs mem secs pow twist Sys one iff aac9716d8ba6: P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs mem secs pow twist Sys one iff aac9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs mem secs pow twist Sys one iff aac9716d8ba6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs mem secs pow twist Sys one iff aac9716d8ba6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSecs.lean#L18-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSecs.lean#L18-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSecs
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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_secs_pow_twistSys_one_iff_aac9716d8ba6 {r : ℕ} (h : Fin (r + 1) → Ω) (n : ℕ) (s : Ω) :
    s ∈ ((twistSys k h 1).pow n).secs ↔ ∀ j, h j ≠ 0 → s / h j ^ n ∈ ampleBase (S := k) h j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleSecs».«mem_secs_pow_twistSys_one_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_secs_pow_twistSys_one_iff_aac9716d8ba6
