-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_vaes_ampleBase_le_chartRing_c0e47ef1f2f5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_vaes_ampleBase_le_chartRing_c0e47ef1f2f5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:57.194172+00:00
-- url     : https://prove2.me/theorems/48f91631-57a8-4531-a9f1-e929edc41c29
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman vaes ample Base le chart Ring c0e47ef1f2f5: P2 M Ground Theory Heights  Heights Kleiman vaes ample Base le chart Ring c0e47ef1f2f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman vaes ample Base le chart Ring c0e47ef1f2f5 construction uses the P2 M Ground Theory Heights  Heights Kleiman vaes ample Base le chart Ring c0e47ef1f2f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleEmbedSections.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleEmbedSections.lean#L20-L22

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_vaes_ampleBase_le_chartRing_c0e47ef1f2f5 {r : ℕ} {h : Fin (r + 1) → Ω} {j : Fin (r + 1)} (hj : h j ≠ 0) :
    ampleBase (S := k) h j ≤ chartRing k h (singleChart hj) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«vaes_ampleBase_le_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_vaes_ampleBase_le_chartRing_c0e47ef1f2f5
