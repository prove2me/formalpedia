-- Prove2me | Theorems.Thm_PascalExtremes_targetB_lower_nonattainment
-- name    : PascalExtremes.targetB_lower_nonattainment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:03:17.004264+00:00
-- url     : https://prove2.me/theorems/a3b93923-e558-44ef-989f-ddf2f88e029b
-- title:
--   Pascal Extremes: target B lower nonattainment
-- statement:
--   Every admissible row strictly below the proposed Target-B row is
--   non-extremal.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetBMinimality.lean#L810-L850
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetBMinimality.lean#L810-L850

module
public import Definitions.Def_PascalExtremes_TargetB
public import Definitions.Def_PascalExtremes_Scaling
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetBMinimality
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.targetB_lower_nonattainment
    {p a N : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hrow : AdmissibleRow (p ^ a + 1) N)
    (hNlt : N < p ^ (3 * a) + 1) :
    padicValNat p (G N (p ^ a + 1)) ≤ a := by sorry
