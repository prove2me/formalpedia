-- Prove2me | Theorems.Thm_Pseudorandom_exp_le_one_add_add_sq_div
-- name    : Pseudorandom.exp_le_one_add_add_sq_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:18.181803+00:00
-- url     : https://prove2.me/theorems/39ac71c2-9402-4177-8b46-a1da6fb14a6f
-- title:
--   Pseudorandom: exp le one add add sq div
-- statement:
--   `e^x ≤ 1 + x + x²/(2(1-r))` whenever `|x| ≤ r < 1`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L33-L65
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L33-L65

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
open Nat

theorem Pseudorandom.exp_le_one_add_add_sq_div (x r : ℝ) (hx : |x| ≤ r) (hr : r < 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - r)) := by sorry
