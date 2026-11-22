-- Prove2me | Theorems.Thm_Pseudorandom_IsExposureMartingale_neg
-- name    : Pseudorandom.IsExposureMartingale.neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:53.057474+00:00
-- url     : https://prove2.me/theorems/97bb4ce5-e505-430f-9d05-3a8df069a46a
-- title:
--   Is Exposure Martingale: neg
-- statement:
--   The Is Exposure Martingale construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L383-L388
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L383-L388

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
public import Theorems.Thm_Pseudorandom_CoordGap_neg
public import Theorems.Thm_Pseudorandom_CoordRare_neg

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}

theorem Pseudorandom.IsExposureMartingale.neg (hX : IsExposureMartingale P X) :
    IsExposureMartingale P (fun k ω => -X k ω) := by sorry
