-- Prove2me | Theorems.Thm_Pseudorandom_CoordRare_neg
-- name    : Pseudorandom.CoordRare.neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:41.376282+00:00
-- url     : https://prove2.me/theorems/f419d75a-bc76-405d-b145-e777a71cdeb6
-- title:
--   Coord Rare: neg
-- statement:
--   The Coord Rare construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L189-L192
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L189-L192

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*}

theorem Pseudorandom.CoordRare.neg {ι : Type*} [DecidableEq ι] {f : (ι → α) → ℝ} {R : ι → Finset α}
    (h : CoordRare f R) : CoordRare (fun ω => -f ω) R := by sorry
