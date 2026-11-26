-- Prove2me | Theorems.Thm_PascalExtremes_targetB_attainment_witness
-- name    : PascalExtremes.targetB_attainment_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:35.583516+00:00
-- url     : https://prove2.me/theorems/2bbc3495-4539-481a-bb87-2383c14c1d33
-- title:
--   Pascal Extremes: target B attainment witness
-- statement:
--   The explicit Stage-3 equality witness at the Target-B row:
--   the selected multiplier is `p^(2a-1)`, and its binomial coefficient has
--   exactly `a+1` carries.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L269-L361
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L269-L361

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.targetB_attainment_witness
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    ∃ k, Admissible (p ^ (3 * a) + 1) (p ^ a + 1) k ∧
      padicValNat p ((p ^ (3 * a) + 1).choose k) = a + 1 := by sorry
