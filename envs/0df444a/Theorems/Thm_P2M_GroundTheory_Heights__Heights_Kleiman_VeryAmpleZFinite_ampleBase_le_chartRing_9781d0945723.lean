-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFinite_ampleBase_le_chartRing_9781d0945723
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFinite_ampleBase_le_chartRing_9781d0945723
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:11:28.369567+00:00
-- url     : https://prove2.me/theorems/e20cc2e6-141b-41ba-aa04-be899659f238
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFinite ample Base le chart Ring 9781d0945723: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFinite ample Base le chart Ring 9781d09457
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFinite ample Base le chart Ring 9781d0945723 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFinite ample Base le chart Ring 9781d0945723 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFinite.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFinite.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFinite
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
open Filter
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFinite
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFinite_ampleBase_le_chartRing_9781d0945723 {h : Fin (r + 1) → Ω} (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) :
    ampleBase (S := S) h j ≤ chartRing S h J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZFinite».«ampleBase_le_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFinite_ampleBase_le_chartRing_9781d0945723
