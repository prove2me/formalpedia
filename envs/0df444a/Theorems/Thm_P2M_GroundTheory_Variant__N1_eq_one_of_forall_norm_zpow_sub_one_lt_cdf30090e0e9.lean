-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_eq_one_of_forall_norm_zpow_sub_one_lt_cdf30090e0e9
-- name    : P2M_GroundTheory_Variant__N1_eq_one_of_forall_norm_zpow_sub_one_lt_cdf30090e0e9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:49.45188+00:00
-- url     : https://prove2.me/theorems/1f366513-09a6-4c3e-a593-de7b1c1e1585
-- title:
--   P2 M Ground Theory Variant  N1 eq one of forall norm zpow sub one lt cdf30090e0e9: P2 M Ground Theory Variant  N1 eq one of forall norm zpow sub one lt cdf30090e0e9
-- statement:
--   The P2 M Ground Theory Variant  N1 eq one of forall norm zpow sub one lt cdf30090e0e9 construction uses the P2 M Ground Theory Variant  N1 eq one of forall norm zpow sub one lt cdf30090e0e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/NormZpow.lean#L5-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/NormZpow.lean#L5-L71

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_eq_one_of_forall_norm_zpow_sub_one_lt_cdf30090e0e9 {z : ℂ} (h : ∀ m : ℤ, ‖z ^ m - 1‖ < 1) :
    z = 1 := by sorry

alias «GroundTheory».«Variant₂».«N1».«eq_one_of_forall_norm_zpow_sub_one_lt» := P2M_GroundTheory_Variant__N1_eq_one_of_forall_norm_zpow_sub_one_lt_cdf30090e0e9
