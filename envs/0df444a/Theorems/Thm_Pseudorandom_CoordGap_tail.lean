-- Prove2me | Theorems.Thm_Pseudorandom_CoordGap_tail
-- name    : Pseudorandom.CoordGap.tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:15.82377+00:00
-- url     : https://prove2.me/theorems/323c06e8-2d33-49f5-8906-e1c63ae45520
-- title:
--   Coord Gap: tail
-- statement:
--   The Coord Gap construction uses the tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L169-L174
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean#L169-L174

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*}

theorem Pseudorandom.CoordGap.tail {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {c : Fin (n + 1) → ℝ}
    (h : CoordGap f c) (b : α) :
    CoordGap (fun ω => f (Fin.cons b ω)) (fun i => c i.succ) := by sorry
