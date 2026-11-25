-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_eq_zero_of_rank_le
-- name    : SNumbers.hilbertNumber_eq_zero_of_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:19:15.207689+00:00
-- url     : https://prove2.me/theorems/acae3803-0b98-4cd6-ab6b-b2d9f8e1fff3
-- title:
--   SNumbers: hilbert Number eq zero of rank le
-- statement:
--   (S4) `rank S ≤ n ⇒ h_n S = 0`, since `rank (B∘S∘A) ≤ rank S ≤ n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L218-L227
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L218-L227

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

theorem SNumbers.hilbertNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) : hilbertNumber S n = 0 := by sorry
