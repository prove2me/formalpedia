-- Prove2me | Theorems.Thm_SNumbers_additive_hilbertNumber
-- name    : SNumbers.additive_hilbertNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:05:47.504128+00:00
-- url     : https://prove2.me/theorems/0033c4c9-328c-50fd-af6e-9e3d2da1673d
-- title:
--   SNumbers: additive hilbert Number
-- statement:
--   The Hilbert numbers are additive: `h_{n+m}(S + T) ≤ hₙ(S) + h_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L423-L425
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L423-L425

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.additive_hilbertNumber :
    Additive (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => hilbertNumber S n) := by sorry
