-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Monic_dvd_of_dvd_C_pow_mul_pow_15cde19839a2
-- name    : P2M_GroundTheory_Heights__Heights_Monic_dvd_of_dvd_C_pow_mul_pow_15cde19839a2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:16.813856+00:00
-- url     : https://prove2.me/theorems/912048e6-6e65-40cb-b684-603413200270
-- title:
--   P2 M Ground Theory Heights  Heights Monic dvd of dvd C pow mul pow 15cde19839a2: P2 M Ground Theory Heights  Heights Monic dvd of dvd C pow mul pow 15cde19839a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Monic dvd of dvd C pow mul pow 15cde19839a2 construction uses the P2 M Ground Theory Heights  Heights Monic dvd of dvd C pow mul pow 15cde19839a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L144-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L144-L168

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Monic_dvd_of_dvd_C_pow_mul_pow_15cde19839a2 {R : Type*} [CommRing R] [IsDomain R] {m u v h : Polynomial R} {c : R}
    (hm : m.Monic) (hc : c ≠ 0) (huv : u * m + v * Polynomial.derivative m = Polynomial.C c) {e N : ℕ}
    (hN : N ≠ 0) (hd : m ∣ Polynomial.C c ^ e * h ^ N) : m ∣ h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Monic».«dvd_of_dvd_C_pow_mul_pow» := P2M_GroundTheory_Heights__Heights_Monic_dvd_of_dvd_C_pow_mul_pow_15cde19839a2
