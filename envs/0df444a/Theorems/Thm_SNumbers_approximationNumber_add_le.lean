-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_add_le
-- name    : SNumbers.approximationNumber_add_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:08:36.721781+00:00
-- url     : https://prove2.me/theorems/89f24764-c071-4a65-8427-35a917b5ce19
-- title:
--   SNumbers: approximation Number add le
-- statement:
--   (S2) `a_n (S + T) ≤ a_n S + ‖T‖`: additivity with `m = 0`, since `a_0 T = ‖T‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L256-L259
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L256-L259

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

theorem SNumbers.approximationNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber (S + T) n ≤ approximationNumber S n + ‖T‖ := by sorry
