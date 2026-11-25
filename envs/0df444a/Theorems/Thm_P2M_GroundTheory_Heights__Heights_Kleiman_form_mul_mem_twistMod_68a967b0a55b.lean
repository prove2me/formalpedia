-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_form_mul_mem_twistMod_68a967b0a55b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_form_mul_mem_twistMod_68a967b0a55b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:48.878656+00:00
-- url     : https://prove2.me/theorems/89145b14-1d41-4aaf-a3e8-ae6186c9fcd4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman form mul mem twist Mod 68a967b0a55b: P2 M Ground Theory Heights  Heights Kleiman form mul mem twist Mod 68a967b0a55b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman form mul mem twist Mod 68a967b0a55b construction uses the P2 M Ground Theory Heights  Heights Kleiman form mul mem twist Mod 68a967b0a55b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L59-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_form_mul_mem_twistMod_68a967b0a55b {h : Poly k N} {d : ℕ} (hh : h.IsHomogeneous d) {c : ℤ} (I : Chart x)
    {o : Ω} (ho : o ∈ twistMod k x c I) : aeval x h * o ∈ twistMod k x (c + d) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«form_mul_mem_twistMod» := P2M_GroundTheory_Heights__Heights_Kleiman_form_mul_mem_twistMod_68a967b0a55b
