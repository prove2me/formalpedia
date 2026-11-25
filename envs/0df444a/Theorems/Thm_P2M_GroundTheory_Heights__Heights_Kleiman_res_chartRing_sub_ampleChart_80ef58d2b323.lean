-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_chartRing_sub_ampleChart_80ef58d2b323
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_chartRing_sub_ampleChart_80ef58d2b323
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:24:40.774096+00:00
-- url     : https://prove2.me/theorems/94c3a1bf-4dc2-4d79-a090-4f21931a388e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res chart Ring sub ample Chart 80ef58d2b323: P2 M Ground Theory Heights  Heights Kleiman res chart Ring sub ample Chart 80ef58d2b323
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res chart Ring sub ample Chart 80ef58d2b323 construction uses the P2 M Ground Theory Heights  Heights Kleiman res chart Ring sub ample Chart 80ef58d2b323 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L99-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {H : SubSystem S x Ω} {σ : Ω} {I : Chart x}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_chartRing_sub_ampleChart_80ef58d2b323 {a : Ω} (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 σ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_chartRing_sub_ampleChart» := P2M_GroundTheory_Heights__Heights_Kleiman_res_chartRing_sub_ampleChart_80ef58d2b323
