-- Prove2me | Theorems.Thm_PascalExtremesPalomar_targetA
-- name    : PascalExtremesPalomar.targetA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:04.571388+00:00
-- url     : https://prove2.me/theorems/ad7be903-86dc-4f71-a7f8-cf3758c4c9ba
-- title:
--   Pascal Extremes Palomar: target A
-- statement:
--   The Pascal Extremes Palomar construction uses the target A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/Solution.lean#L38-L47
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/Solution.lean#L38-L47

module
public import Definitions.Def_PascalExtremes
public import Definitions.Def_PascalExtremes_Solution
public import Theorems.Thm_PascalExtremes_targetA

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremesPalomar

theorem PascalExtremesPalomar.targetA
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    IsGreatest
      {v : ℕ | ∃ N, AdmissibleRow m N ∧
        padicValNat p (G N m) = v}
      (rP p m) := by sorry
