-- Prove2me | Theorems.Thm_PascalExtremes_targetB_lower_multiplier_witness
-- name    : PascalExtremes.targetB_lower_multiplier_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:03:04.296837+00:00
-- url     : https://prove2.me/theorems/75d1b6cd-7365-4e6c-89af-95616ee57976
-- title:
--   Pascal Extremes: target B lower multiplier witness
-- statement:
--   Every multiplier below `q0` has an explicit selected coefficient of
--   valuation at most `a`. This follows the Stage-3 leading split, switching
--   to the fixed fallback `p^(a-1)` exactly when the leading split's coarse
--   carry bound is not strict enough.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetBMinimality.lean#L410-L805
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetBMinimality.lean#L410-L805

module
public import Definitions.Def_PascalExtremes_TargetB
public import Definitions.Def_PascalExtremes_Scaling
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetBMinimality
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.targetB_lower_multiplier_witness
    {p a q : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hq2 : 2 ≤ q) (hqlt : q < q0 p a) :
    ∃ d, 0 < d ∧ d < q ∧
      padicValNat p
        (((p ^ a + 1) * q).choose ((p ^ a + 1) * d)) ≤ a := by sorry
