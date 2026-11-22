-- Prove2me | Theorems.Thm_Pseudorandom_Adapted_mono
-- name    : Pseudorandom.Adapted.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:10.274801+00:00
-- url     : https://prove2.me/theorems/b7788997-b389-4022-8b4b-9134bcd52c49
-- title:
--   Adapted: mono
-- statement:
--   The Adapted construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L76-L78
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L76-L78

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
omit [Fintype α]

theorem Pseudorandom.Adapted.mono {β : Type*} {k k' : ℕ} {F : (Fin n → α) → β} (h : Adapted k F)
    (hk : k ≤ k') : Adapted k' F := by sorry
