-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_chartRing_of_mul_eq_one_e838a6f7d60a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_chartRing_of_mul_eq_one_e838a6f7d60a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:36.480307+00:00
-- url     : https://prove2.me/theorems/5a80ac3a-56ea-4947-ac4b-fd9ddfcc1f45
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mul mem chart Ring of mul eq one e838a6f7d60a: P2 M Ground Theory Heights  Heights Kleiman mul mem chart Ring of mul eq one e838a6f7d60a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mul mem chart Ring of mul eq one e838a6f7d60a construction uses the P2 M Ground Theory Heights  Heights Kleiman mul mem chart Ring of mul eq one e838a6f7d60a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L13-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_chartRing_of_mul_eq_one_e838a6f7d60a {S : Type u} [CommRing S] {Ω : Type w} [Field Ω]
    [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {I : Chart x} {P M : Submodule (chartRing S x I) Ω}
    (hPM : P * M = 1) {q m : Ω} (hq : q ∈ P) (hm : m ∈ M) : q * m ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mul_mem_chartRing_of_mul_eq_one» := P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_chartRing_of_mul_eq_one_e838a6f7d60a
