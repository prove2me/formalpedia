-- Prove2me | Theorems.Thm_PascalExtremesPalomar_targetB
-- name    : PascalExtremesPalomar.targetB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:55.693869+00:00
-- url     : https://prove2.me/theorems/8b28fbf6-3fd1-45c8-848d-28e2c74fe0dd
-- title:
--   Pascal Extremes Palomar: target B
-- statement:
--   The Pascal Extremes Palomar construction uses the target B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/Solution.lean#L56-L63
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/Solution.lean#L56-L63

module
public import Definitions.Def_PascalExtremes
public import Definitions.Def_PascalExtremes_Solution
public import Theorems.Thm_PascalExtremes_targetB

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremesPalomar

theorem PascalExtremesPalomar.targetB
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    T p (p ^ a + 1) = p ^ (3 * a) + 1 := by sorry
