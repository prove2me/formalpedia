-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_twist_comm_3dd36e957fe6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_twist_comm_3dd36e957fe6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:41:27.524704+00:00
-- url     : https://prove2.me/theorems/9088fd90-83c1-4a7c-8e4c-8c7c8da2f359
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Pows twist comm 3dd36e957fe6: P2 M Ground Theory Heights  Heights Kleiman twist Pows twist comm 3dd36e957fe6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Pows twist comm 3dd36e957fe6 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Pows twist comm 3dd36e957fe6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L22-L28

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_twist_comm_3dd36e957fe6 (F Q : SubSystem S x Ω) :
    ∀ (t : ℕ) (L : Fin t → SubSystem S x Ω) (n : Fin t → ℕ),
      (F.twist Q).twistPows t L n = (F.twistPows t L n).twist Q
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistPows_twist_comm» := P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_twist_comm_3dd36e957fe6
