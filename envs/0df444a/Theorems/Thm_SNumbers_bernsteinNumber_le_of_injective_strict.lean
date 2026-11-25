-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_le_of_injective_strict
-- name    : SNumbers.bernsteinNumber_le_of_injective_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:11:46.980064+00:00
-- url     : https://prove2.me/theorems/4526c31f-6044-5766-8164-e62bfdefae89
-- title:
--   SNumbers: bernstein Number le of injective strict
-- statement:
--   **The Bernstein numbers are the smallest injective strict `s`-number
--   sequence.** For every injective strict `s`-number sequence `s`,
--   `bₙ(S) ≤ sₙ(S)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L588-L629
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L588-L629

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

theorem SNumbers.bernsteinNumber_le_of_injective_strict {s : Family 𝕜}
    (hs : IsStrictSNumberSequence s) (hinj : Injective s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n ≤ s S n := by sorry
