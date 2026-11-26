-- Prove2me | Theorems.Thm_PascalExtremes_targetA_upper_witness
-- name    : PascalExtremes.targetA_upper_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:11.64432+00:00
-- url     : https://prove2.me/theorems/7013bd67-ad21-5509-a9ab-88363bc9a075
-- title:
--   Pascal Extremes: target A upper witness
-- statement:
--   The leading-base-`p`-digit witness from Stage 3. Every admissible row
--   contains a selected coefficient whose valuation is at most `rP p m`.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetA.lean#L22-L187
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetA.lean#L22-L187

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Powers
public import Definitions.Def_PascalExtremes_CarryBounds
public import Mathlib.Tactic
public import Definitions.Def_PascalExtremes_TargetA
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.targetA_upper_witness
    {p m N : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m)
    (hrow : AdmissibleRow m N) :
    ∃ k, Admissible N m k ∧
      padicValNat p (N.choose k) ≤ rP p m := by sorry
