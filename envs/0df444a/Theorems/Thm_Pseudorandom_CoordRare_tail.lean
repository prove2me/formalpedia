-- Prove2me | Theorems.Thm_Pseudorandom_CoordRare_tail
-- name    : Pseudorandom.CoordRare.tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:33.712742+00:00
-- url     : https://prove2.me/theorems/c180a443-2ef8-415c-ad77-68939df96da9
-- title:
--   Coord Rare: tail
-- statement:
--   The Coord Rare construction uses the tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L176-L181
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L176-L181

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*}

theorem Pseudorandom.CoordRare.tail {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {R : Fin (n + 1) → Finset α}
    (h : CoordRare f R) (b : α) :
    CoordRare (fun ω => f (Fin.cons b ω)) (fun i => R i.succ) := by sorry
