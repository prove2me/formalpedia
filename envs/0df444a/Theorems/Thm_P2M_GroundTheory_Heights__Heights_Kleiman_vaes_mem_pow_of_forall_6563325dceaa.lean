-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_vaes_mem_pow_of_forall_6563325dceaa
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_vaes_mem_pow_of_forall_6563325dceaa
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:52.30898+00:00
-- url     : https://prove2.me/theorems/bb06b87f-b916-43d1-b0f5-f453a87007e4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman vaes mem pow of forall 6563325dceaa: P2 M Ground Theory Heights  Heights Kleiman vaes mem pow of forall 6563325dceaa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman vaes mem pow of forall 6563325dceaa construction uses the P2 M Ground Theory Heights  Heights Kleiman vaes mem pow of forall 6563325dceaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleEmbedSections.lean#L24-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleEmbedSections.lean#L24-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedSectionsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleEmbedSections
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {y : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_vaes_mem_pow_of_forall_6563325dceaa (Q : LineBundle k y) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Q.toSubSystem h) (I : Chart y) {m : ℕ} {s : Ω}
    (hs : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ (Q.toSubSystem.pow (m + e)).sub I) :
    s ∈ (Q.toSubSystem.pow m).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«vaes_mem_pow_of_forall» := P2M_GroundTheory_Heights__Heights_Kleiman_vaes_mem_pow_of_forall_6563325dceaa
