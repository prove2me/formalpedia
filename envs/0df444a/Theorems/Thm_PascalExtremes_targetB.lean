-- Prove2me | Theorems.Thm_PascalExtremes_targetB
-- name    : PascalExtremes.targetB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:03:00.576812+00:00
-- url     : https://prove2.me/theorems/9eee7633-0b2a-57f4-844e-268464b38c59
-- title:
--   Pascal Extremes: target B
-- statement:
--   Target B: the first Target-A extremal row for `m = p^a+1` is
--   `p^(3a)+1`.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetBMinimality.lean#L854-L888
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetBMinimality.lean#L854-L888

module
public import Definitions.Def_PascalExtremes_TargetB
public import Definitions.Def_PascalExtremes_Scaling
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetBMinimality
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.targetB
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    T p (p ^ a + 1) = p ^ (3 * a) + 1 := by sorry
