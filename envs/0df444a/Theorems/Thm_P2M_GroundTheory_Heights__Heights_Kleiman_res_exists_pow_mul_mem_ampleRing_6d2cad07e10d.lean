-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_ampleRing_6d2cad07e10d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_ampleRing_6d2cad07e10d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:02:07.617374+00:00
-- url     : https://prove2.me/theorems/0125329b-4a48-4963-8ae5-7eafbe8ba33e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res exists pow mul mem ample Ring 6d2cad07e10d: P2 M Ground Theory Heights  Heights Kleiman res exists pow mul mem ample Ring 6d2cad07e10d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res exists pow mul mem ample Ring 6d2cad07e10d construction uses the P2 M Ground Theory Heights  Heights Kleiman res exists pow mul mem ample Ring 6d2cad07e10d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L198-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L198-L239

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_ampleRing_6d2cad07e10d (H : LineBundle S x) {σ b : Ω} {J : Chart x}
    (hb : b ∈ ampleRing H.toSubSystem 1 σ)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H.toSubSystem 1 σ I)
    {z : Ω} (hz : z ∈ ampleChart H.toSubSystem 1 σ J) :
    ∃ E : ℕ, b ^ E * z ∈ ampleRing H.toSubSystem 1 σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_exists_pow_mul_mem_ampleRing» := P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_ampleRing_6d2cad07e10d
