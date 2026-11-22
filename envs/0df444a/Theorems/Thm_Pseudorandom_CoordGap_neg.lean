-- Prove2me | Theorems.Thm_Pseudorandom_CoordGap_neg
-- name    : Pseudorandom.CoordGap.neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:30.247584+00:00
-- url     : https://prove2.me/theorems/fce159df-90f1-4195-921b-20282e739b62
-- title:
--   Coord Gap: neg
-- statement:
--   The Coord Gap construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L183-L187
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L183-L187

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*}

theorem Pseudorandom.CoordGap.neg {ι : Type*} [DecidableEq ι] {f : (ι → α) → ℝ} {c : ι → ℝ}
    (h : CoordGap f c) : CoordGap (fun ω => -f ω) c := by sorry
