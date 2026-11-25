-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_twist_8ff7324980c5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_twist_8ff7324980c5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:00:47.10488+00:00
-- url     : https://prove2.me/theorems/776e557c-2d63-5bff-ae4c-54489235c149
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ZChart Local loc twist 8ff7324980c5: P2 M Ground Theory Heights  Heights Kleiman ZChart Local loc twist 8ff7324980c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ZChart Local loc twist 8ff7324980c5 construction uses the P2 M Ground Theory Heights  Heights Kleiman ZChart Local loc twist 8ff7324980c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L73-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L73-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZChartLocal
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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.ZChartLocal
open AmpleAffineGen AmpleTwistLocal
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_twist_8ff7324980c5 (G : SubFamily S x E) (H : LineBundle S x) (I K : Chart x) (q : ℕ) {y : E}
    (hy : y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub (unionChart I K)) :
    ∃ c : ℕ, chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ZChartLocal».«loc_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_twist_8ff7324980c5
