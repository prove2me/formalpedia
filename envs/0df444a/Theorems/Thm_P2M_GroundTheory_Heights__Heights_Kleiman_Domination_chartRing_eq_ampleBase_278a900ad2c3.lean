-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_chartRing_eq_ampleBase_278a900ad2c3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_chartRing_eq_ampleBase_278a900ad2c3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:40.505782+00:00
-- url     : https://prove2.me/theorems/dfe8bd7b-d443-4815-8143-7116b5ce2940
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination chart Ring eq ample Base 278a900ad2c3: P2 M Ground Theory Heights  Heights Kleiman Domination chart Ring eq ample Base 278a900ad2c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination chart Ring eq ample Base 278a900ad2c3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination chart Ring eq ample Base 278a900ad2c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L117-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L117-L124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
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
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_chartRing_eq_ampleBase_278a900ad2c3 {i : Fin (N + 1)} (hi : x i ≠ 0) :
    chartRing S x (singleChart hi) = ampleBase (S := S) x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«chartRing_eq_ampleBase» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_chartRing_eq_ampleBase_278a900ad2c3
