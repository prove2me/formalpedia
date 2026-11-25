-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_le_one_add_sum_norm_coeff_of_monic_44e00fccf80b
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_le_one_add_sum_norm_coeff_of_monic_44e00fccf80b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:35.623824+00:00
-- url     : https://prove2.me/theorems/35dea611-164c-401f-ac90-b80080650788
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel norm le one add sum norm coeff of monic 44e00fccf80b: P2 M Ground Theory Heights  Heights Hilbert Samuel norm le one add sum norm coeff of monic 44e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel norm le one add sum norm coeff of monic 44e00fccf80b construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel norm le one add sum norm coeff of monic 44e00fccf80b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PMonicRootGrowth.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PMonicRootGrowth.lean#L25-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PMonicRootGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_le_one_add_sum_norm_coeff_of_monic_44e00fccf80b {q : Polynomial ℂ} (hq : q.Monic) {τ : ℂ}
    (hτ : q.IsRoot τ) : ‖τ‖ ≤ 1 + ∑ i ∈ range q.natDegree, ‖q.coeff i‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«norm_le_one_add_sum_norm_coeff_of_monic» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_le_one_add_sum_norm_coeff_of_monic_44e00fccf80b
