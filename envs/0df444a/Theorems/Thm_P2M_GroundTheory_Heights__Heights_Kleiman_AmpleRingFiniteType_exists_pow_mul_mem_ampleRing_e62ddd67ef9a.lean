-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_exists_pow_mul_mem_ampleRing_e62ddd67ef9a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_exists_pow_mul_mem_ampleRing_e62ddd67ef9a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:52:57.110601+00:00
-- url     : https://prove2.me/theorems/c20188fa-04eb-54e4-b926-30dc05767c13
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type exists pow mul mem ample Ring e62ddd67ef9a: P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type exists pow mul mem amp
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type exists pow mul mem ample Ring e62ddd67ef9a construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type exists pow mul mem ample Ring e62ddd67ef9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L124-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L124-L153

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFiniteType
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_exists_pow_mul_mem_ampleRing_e62ddd67ef9a (H : LineBundle S x) {m : ℕ} {h : Ω}
    (hh : ∀ I, h ∈ (H.pow m).sub I) {c : Ω} (hc : c ∈ ampleRing H.toSubSystem m h) (J : Chart x)
    (hrat : ∀ I : Chart x, ∃ e : ℕ,
      c ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H.toSubSystem m h I)
    {y : Ω} (hy : y ∈ chartRing S x J) : ∃ M : ℕ, c ^ M * y ∈ ampleRing H.toSubSystem m h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleRingFiniteType».«exists_pow_mul_mem_ampleRing» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_exists_pow_mul_mem_ampleRing_e62ddd67ef9a
