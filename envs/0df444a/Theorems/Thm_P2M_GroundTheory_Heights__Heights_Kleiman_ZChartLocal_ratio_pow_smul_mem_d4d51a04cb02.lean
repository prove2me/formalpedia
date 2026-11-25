-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_ratio_pow_smul_mem_d4d51a04cb02
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_ratio_pow_smul_mem_d4d51a04cb02
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:00:43.201459+00:00
-- url     : https://prove2.me/theorems/c30f654c-f6f7-4f44-a539-7db4151ea994
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ZChart Local ratio pow smul mem d4d51a04cb02: P2 M Ground Theory Heights  Heights Kleiman ZChart Local ratio pow smul mem d4d51a04cb02
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ZChart Local ratio pow smul mem d4d51a04cb02 construction uses the P2 M Ground Theory Heights  Heights Kleiman ZChart Local ratio pow smul mem d4d51a04cb02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L52-L54

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_ratio_pow_smul_mem_d4d51a04cb02 (F : SubSystem S x E) (I K : Chart x) (k : ℕ) {y : E} (hy : y ∈ F.sub I) :
    chartRatio I K ^ k • y ∈ F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ZChartLocal».«ratio_pow_smul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_ratio_pow_smul_mem_d4d51a04cb02
