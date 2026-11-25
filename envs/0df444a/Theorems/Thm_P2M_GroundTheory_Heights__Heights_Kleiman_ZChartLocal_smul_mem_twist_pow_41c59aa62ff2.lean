-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_smul_mem_twist_pow_41c59aa62ff2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_smul_mem_twist_pow_41c59aa62ff2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:08.40048+00:00
-- url     : https://prove2.me/theorems/b24e8f91-d6aa-4d10-b613-23b8ccc834c2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ZChart Local smul mem twist pow 41c59aa62ff2: P2 M Ground Theory Heights  Heights Kleiman ZChart Local smul mem twist pow 41c59aa62ff2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ZChart Local smul mem twist pow 41c59aa62ff2 construction uses the P2 M Ground Theory Heights  Heights Kleiman ZChart Local smul mem twist pow 41c59aa62ff2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L22-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L22-L37

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_smul_mem_twist_pow_41c59aa62ff2 (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ}
    {y : E} {w : Ω} (hy : y ∈ (F.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    w • y ∈ (F.twist (H.pow (c + d))).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ZChartLocal».«smul_mem_twist_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_smul_mem_twist_pow_41c59aa62ff2
