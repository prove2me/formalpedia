-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_pow_div_xProd_mem_d75dc4a6d385
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_pow_div_xProd_mem_d75dc4a6d385
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:59:48.034031+00:00
-- url     : https://prove2.me/theorems/3a207653-8e20-5f25-9424-e5d7a06272a0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring pow div x Prod mem d75dc4a6d385: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring pow div x Prod mem d75dc4a6d385
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring pow div x Prod mem d75dc4a6d385 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring pow div x Prod mem d75dc4a6d385 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartRing.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartRing.lean#L55-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZChartRing
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartRing
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_pow_div_xProd_mem_d75dc4a6d385 {r : ℕ} {h : Fin (r + 1) → Ω} (J : Chart h) (j : Fin (r + 1)) :
    h j ^ J.1.card / xProd J ∈ chartRing S h J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZChartRing».«pow_div_xProd_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_pow_div_xProd_mem_d75dc4a6d385
