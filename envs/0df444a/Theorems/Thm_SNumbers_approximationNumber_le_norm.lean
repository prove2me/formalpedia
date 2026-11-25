-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_norm
-- name    : SNumbers.approximationNumber_le_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:08:31.077793+00:00
-- url     : https://prove2.me/theorems/9d6b5b31-122e-4e39-a337-ad9545971391
-- title:
--   SNumbers: approximation Number le norm
-- statement:
--   Upper bound by the operator norm: `a_n S ≤ ‖S‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L142-L145
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L142-L145

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

theorem SNumbers.approximationNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ ‖S‖ := by sorry
