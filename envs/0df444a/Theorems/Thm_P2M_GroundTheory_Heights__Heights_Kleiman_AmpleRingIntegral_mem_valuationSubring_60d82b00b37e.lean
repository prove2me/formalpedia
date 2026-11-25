-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingIntegral_mem_valuationSubring_60d82b00b37e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingIntegral_mem_valuationSubring_60d82b00b37e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:08.425545+00:00
-- url     : https://prove2.me/theorems/aac11b41-f3de-55df-ae5e-777729e9f122
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Ring Integral mem valuation Subring 60d82b00b37e: P2 M Ground Theory Heights  Heights Kleiman Ample Ring Integral mem valuation Subring 60d82b00b37e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Ring Integral mem valuation Subring 60d82b00b37e construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Ring Integral mem valuation Subring 60d82b00b37e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingIntegral.lean#L14-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingIntegral.lean#L14-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingIntegral
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleRingIntegral
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingIntegral_mem_valuationSubring_60d82b00b37e {H : LineBundle S x} (D : AmpleData S x H) (j : Fin (D.r + 1))
    (hj : D.h j ≠ 0) (hne : (support x).Nonempty) (V : ValuationSubring Ω)
    (hV : (ampleBase (S := S) D.h j : Set Ω) ⊆ V) {f : Ω}
    (hf : f ∈ ampleRing H.toSubSystem D.m (D.h j)) : f ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleRingIntegral».«mem_valuationSubring» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingIntegral_mem_valuationSubring_60d82b00b37e
