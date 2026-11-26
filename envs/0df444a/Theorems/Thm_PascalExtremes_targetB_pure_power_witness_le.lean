-- Prove2me | Theorems.Thm_PascalExtremes_targetB_pure_power_witness_le
-- name    : PascalExtremes.targetB_pure_power_witness_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:03:07.571996+00:00
-- url     : https://prove2.me/theorems/23bf41d5-7615-48d3-8a78-6dc30088f447
-- title:
--   Pascal Extremes: target B pure power witness le
-- statement:
--   Pure-power multiplier branch of the strict lower-row argument.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetBMinimality.lean#L92-L118
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetBMinimality.lean#L92-L118

module
public import Definitions.Def_PascalExtremes_TargetB
public import Definitions.Def_PascalExtremes_Scaling
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetBMinimality
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.targetB_pure_power_witness_le
    {p a t : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (ht : 1 ≤ t) :
    padicValNat p
      (((p ^ a + 1) * p ^ t).choose
        ((p ^ a + 1) * p ^ (t - 1))) ≤ a := by sorry
