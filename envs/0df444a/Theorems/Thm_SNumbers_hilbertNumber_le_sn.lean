-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_le_sn
-- name    : SNumbers.hilbertNumber_le_sn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:22:01.323153+00:00
-- url     : https://prove2.me/theorems/1195f799-77a5-4bb5-8794-7e57c763231c
-- title:
--   SNumbers: hilbert Number le sn
-- statement:
--   **Lower bound.** The Hilbert numbers are the smallest `s`-number
--   sequence: `hₙ(S) ≤ sₙ(S)` for every `s`-number sequence `s`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L123-L135
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L123-L135

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.hilbertNumber_le_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ s S n := by sorry
