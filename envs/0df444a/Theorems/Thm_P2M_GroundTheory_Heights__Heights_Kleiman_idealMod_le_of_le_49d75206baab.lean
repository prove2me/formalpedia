-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_of_le_49d75206baab
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_of_le_49d75206baab
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:11:12.03056+00:00
-- url     : https://prove2.me/theorems/419fa8ca-b2dc-4e8e-bc73-c8a3c871edde
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Mod le of le 49d75206baab: P2 M Ground Theory Heights  Heights Kleiman ideal Mod le of le 49d75206baab
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Mod le of le 49d75206baab construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Mod le of le 49d75206baab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L51-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_of_le_49d75206baab {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    idealMod J I ≤ idealMod J' I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealMod_le_of_le» := P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_of_le_49d75206baab
