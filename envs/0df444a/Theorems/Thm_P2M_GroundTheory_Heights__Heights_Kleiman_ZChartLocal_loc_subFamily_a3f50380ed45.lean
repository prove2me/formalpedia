-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_subFamily_a3f50380ed45
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_subFamily_a3f50380ed45
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:02:50.509021+00:00
-- url     : https://prove2.me/theorems/f58521e6-3054-5f31-b1a3-b37624bf46cd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ZChart Local loc sub Family a3f50380ed45: P2 M Ground Theory Heights  Heights Kleiman ZChart Local loc sub Family a3f50380ed45
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ZChart Local loc sub Family a3f50380ed45 construction uses the P2 M Ground Theory Heights  Heights Kleiman ZChart Local loc sub Family a3f50380ed45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L58-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L58-L69

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_subFamily_a3f50380ed45 (G : SubFamily S x E) (I K : Chart x) {y : E}
    (hy : y ∈ G.sub (unionChart I K)) : ∃ c : ℕ, chartRatio I K ^ c • y ∈ G.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ZChartLocal».«loc_subFamily» := P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_subFamily_a3f50380ed45
