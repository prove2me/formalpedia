-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
-- name    : SNumbers.approximationNumber_le_norm_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:43:53.316744+00:00
-- url     : https://prove2.me/theorems/3e40404c-784d-4fe6-8b11-b21aeaf9788d
-- title:
--   SNumbers: approximation Number le norm sub
-- statement:
--   Convenience: every operator `L` of rank ≤ n provides an upper bound for
--   the approximation number.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L99-L102
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L99-L102

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.approximationNumber_le_norm_sub {S : X →L[𝕜] Y} {n : ℕ}
    {L : X →L[𝕜] Y} (hL : L.rank ≤ (n : Cardinal)) :
    approximationNumber S n ≤ ‖S - L‖ := by sorry
