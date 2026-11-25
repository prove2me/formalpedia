-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_div_mem_chartRing_d354e0157f48
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_div_mem_chartRing_d354e0157f48
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:23.837799+00:00
-- url     : https://prove2.me/theorems/4e2bb2ac-005e-49dc-808f-57e8168f720c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt div mem chart Ring d354e0157f48: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt div mem chart Ring d354e0157f48
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt div mem chart Ring d354e0157f48 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt div mem chart Ring d354e0157f48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L54-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
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
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_div_mem_chartRing_d354e0157f48 (I : Chart x) (j : Fin (N + 1)) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    x j / x i ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«div_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_div_mem_chartRing_d354e0157f48
