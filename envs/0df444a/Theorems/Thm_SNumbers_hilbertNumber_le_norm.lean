-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_le_norm
-- name    : SNumbers.hilbertNumber_le_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:24:38.041302+00:00
-- url     : https://prove2.me/theorems/860a3952-07c5-4f14-8309-58c7484759de
-- title:
--   SNumbers: hilbert Number le norm
-- statement:
--   (S1a, easy half) `h_n S ≤ ‖S‖`, since `h_n S ≤ h_0 S = ‖S‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L296-L298
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L296-L298

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

theorem SNumbers.hilbertNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) : hilbertNumber S n ≤ ‖S‖ := by sorry
