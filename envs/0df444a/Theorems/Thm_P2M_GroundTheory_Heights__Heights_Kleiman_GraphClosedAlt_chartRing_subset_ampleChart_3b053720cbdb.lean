-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_chartRing_subset_ampleChart_3b053720cbdb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_chartRing_subset_ampleChart_3b053720cbdb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:06:10.39475+00:00
-- url     : https://prove2.me/theorems/1d05570a-8449-4016-871f-07f8952d6126
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt chart Ring subset ample Chart 3b053720cbdb: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt chart Ring subset ample Chart 3b05
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt chart Ring subset ample Chart 3b053720cbdb construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt chart Ring subset ample Chart 3b053720cbdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L19-L28

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_chartRing_subset_ampleChart_3b053720cbdb (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 h I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«chartRing_subset_ampleChart» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_chartRing_subset_ampleChart_3b053720cbdb
