-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_chartRing_806e14e20021
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_chartRing_806e14e20021
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:55.356008+00:00
-- url     : https://prove2.me/theorems/ad23c49d-5e33-4e6f-a8d3-5ceedf1e1a51
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res exists pow mul mem chart Ring 806e14e20021: P2 M Ground Theory Heights  Heights Kleiman res exists pow mul mem chart Ring 806e14e20021
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res exists pow mul mem chart Ring 806e14e20021 construction uses the P2 M Ground Theory Heights  Heights Kleiman res exists pow mul mem chart Ring 806e14e20021 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L128-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L128-L196

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_chartRing_806e14e20021 (I J : Chart x) {u : Ω}
    (hu : u ∈ chartRing S x (resUnionChart x I J)) :
    ∃ M : ℕ, (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * u ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_exists_pow_mul_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_chartRing_806e14e20021
