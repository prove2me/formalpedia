-- Prove2me | Theorems.Thm_PascalExtremes_targetA
-- name    : PascalExtremes.targetA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:46.143333+00:00
-- url     : https://prove2.me/theorems/687924c9-6703-48ec-b263-0aea0f3f504c
-- title:
--   Pascal Extremes: target A
-- statement:
--   Exact maximum formulation of Target A.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetAAttainment.lean#L382-L392
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetAAttainment.lean#L382-L392

module
public import Definitions.Def_PascalExtremes_TargetA
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetAAttainment
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.targetA
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    IsGreatest
      {v : ℕ | ∃ N, AdmissibleRow m N ∧
        padicValNat p (G N m) = v}
      (rP p m) := by sorry
