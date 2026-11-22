-- Prove2me | Theorems.Thm_Pseudorandom_pE_resample
-- name    : Pseudorandom.pE_resample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:14.792409+00:00
-- url     : https://prove2.me/theorems/8370e688-e878-4264-8604-5e02f6fddf45
-- title:
--   Pseudorandom: p E resample
-- statement:
--   Resampling one coordinate does not change the expectation.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L35-L63
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean#L35-L63

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}

theorem Pseudorandom.pE_resample (hP : IsPMF P) (i : ι) (g : (ι → α) → ℝ) :
    pE P (fun ω => ∑ a, P i a * g (Function.update ω i a)) = pE P g := by sorry
