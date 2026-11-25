-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_one_81e38c4bffc4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_one_81e38c4bffc4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:26.888325+00:00
-- url     : https://prove2.me/theorems/d69b91ab-4fed-569c-8cfb-5ffb65e83022
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Mod le one 81e38c4bffc4: P2 M Ground Theory Heights  Heights Kleiman ideal Mod le one 81e38c4bffc4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Mod le one 81e38c4bffc4 construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Mod le one 81e38c4bffc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L46-L49

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_one_81e38c4bffc4 (J : Ideal (Poly S N)) (I : Chart x) : idealMod J I ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealMod_le_one» := P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_one_81e38c4bffc4
