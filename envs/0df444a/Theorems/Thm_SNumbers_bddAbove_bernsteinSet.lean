-- Prove2me | Theorems.Thm_SNumbers_bddAbove_bernsteinSet
-- name    : SNumbers.bddAbove_bernsteinSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:56:21.60042+00:00
-- url     : https://prove2.me/theorems/96941816-738e-4206-b474-739395209752
-- title:
--   SNumbers: bdd Above bernstein Set
-- statement:
--   The set of admissible gains is bounded above by `‖S‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L120-L122
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L120-L122

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

theorem SNumbers.bddAbove_bernsteinSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddAbove (bernsteinSet S n) := by sorry
