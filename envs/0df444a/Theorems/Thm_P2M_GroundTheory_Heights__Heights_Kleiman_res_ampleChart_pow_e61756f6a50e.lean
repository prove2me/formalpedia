-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_ampleChart_pow_e61756f6a50e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_ampleChart_pow_e61756f6a50e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:55.670867+00:00
-- url     : https://prove2.me/theorems/3759bcd5-3adb-4424-a90b-60d2e9d2aacf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res ample Chart pow e61756f6a50e: P2 M Ground Theory Heights  Heights Kleiman res ample Chart pow e61756f6a50e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res ample Chart pow e61756f6a50e construction uses the P2 M Ground Theory Heights  Heights Kleiman res ample Chart pow e61756f6a50e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L102-L106

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_ampleChart_pow_e61756f6a50e {a : Ω} (ha : a ∈ ampleChart H 1 σ I) (n : ℕ) :
    a ^ n ∈ ampleChart H 1 σ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_ampleChart_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_res_ampleChart_pow_e61756f6a50e
