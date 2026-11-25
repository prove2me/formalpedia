-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_secs_twistBundle_zero_iff_78d23409d145
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_secs_twistBundle_zero_iff_78d23409d145
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:33.460896+00:00
-- url     : https://prove2.me/theorems/99bc5c56-8b03-4e4f-a53e-67b423a87402
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination mem secs twist Bundle zero iff 78d23409d145: P2 M Ground Theory Heights  Heights Kleiman Domination mem secs twist Bundle zero iff 78d23409d145
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination mem secs twist Bundle zero iff 78d23409d145 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination mem secs twist Bundle zero iff 78d23409d145 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L237-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L237-L240

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
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)
omit [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_secs_twistBundle_zero_iff_78d23409d145 {R : Type*} [CommRing R] [Algebra R Ω] (z : Ω) :
    z ∈ (twistBundle R x' 0).secs ↔ ∀ J : Chart x', z ∈ chartRing R x' J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«mem_secs_twistBundle_zero_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_secs_twistBundle_zero_iff_78d23409d145
