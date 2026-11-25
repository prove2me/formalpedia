-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_le_norm
-- name    : SNumbers.bernsteinNumber_le_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:02:17.069805+00:00
-- url     : https://prove2.me/theorems/4a649862-a353-59e6-9a33-e642e3108a07
-- title:
--   SNumbers: bernstein Number le norm
-- statement:
--   Upper bound by the operator norm: `b_n S ≤ ‖S‖`, since `b_n S ≤ b_0 S = ‖S‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L222-L225
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L222-L225

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
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

theorem SNumbers.bernsteinNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n ≤ ‖S‖ := by sorry
