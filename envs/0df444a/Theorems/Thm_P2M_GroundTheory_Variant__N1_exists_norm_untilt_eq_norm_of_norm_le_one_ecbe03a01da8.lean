-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_norm_untilt_eq_norm_of_norm_le_one_ecbe03a01da8
-- name    : P2M_GroundTheory_Variant__N1_exists_norm_untilt_eq_norm_of_norm_le_one_ecbe03a01da8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:59.524902+00:00
-- url     : https://prove2.me/theorems/7c36ae2c-f601-48d1-9484-fe05b185ff0b
-- title:
--   P2 M Ground Theory Variant  N1 exists norm untilt eq norm of norm le one ecbe03a01da8: P2 M Ground Theory Variant  N1 exists norm untilt eq norm of norm le one ecbe03a01da8
-- statement:
--   The P2 M Ground Theory Variant  N1 exists norm untilt eq norm of norm le one ecbe03a01da8 construction uses the P2 M Ground Theory Variant  N1 exists norm untilt eq norm of norm le one ecbe03a01da8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/TiltCountableNeighbourhoods.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/TiltCountableNeighbourhoods.lean#L81-L87

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open GroundTheory.PAdicHodge

theorem P2M_GroundTheory_Variant__N1_exists_norm_untilt_eq_norm_of_norm_le_one_ecbe03a01da8 {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] {p : ℕ} [Fact (Nat.Prime p)] [IsPerfectoidField K p] {y : K}
    (hy : y ≠ 0) (hy1 : ‖y‖ ≤ 1) :
    ∃ a : PreTilt (normInteger K) p, ‖((PreTilt.untilt a : normInteger K) : K)‖ = ‖y‖ := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_norm_untilt_eq_norm_of_norm_le_one» := P2M_GroundTheory_Variant__N1_exists_norm_untilt_eq_norm_of_norm_le_one_ecbe03a01da8
