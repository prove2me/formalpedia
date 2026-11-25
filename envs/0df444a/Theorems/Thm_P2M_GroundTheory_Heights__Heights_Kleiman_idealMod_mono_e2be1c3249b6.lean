-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mono_e2be1c3249b6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mono_e2be1c3249b6
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:22:42.871021+00:00
-- url     : https://prove2.me/theorems/3bbdbbaf-109b-4eba-bfb9-fd706314b278
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Mod mono e2be1c3249b6: P2 M Ground Theory Heights  Heights Kleiman ideal Mod mono e2be1c3249b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Mod mono e2be1c3249b6 construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Mod mono e2be1c3249b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L27-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mono_e2be1c3249b6 {J J' : Ideal (Poly k N)} (h : J ≤ J') (I : Chart x) :
    idealMod (x := x) J I ≤ idealMod (x := x) J' I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealMod_mono» := P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mono_e2be1c3249b6
