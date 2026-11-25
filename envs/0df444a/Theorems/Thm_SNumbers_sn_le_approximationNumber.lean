-- Prove2me | Theorems.Thm_SNumbers_sn_le_approximationNumber
-- name    : SNumbers.sn_le_approximationNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:47:13.43381+00:00
-- url     : https://prove2.me/theorems/f2d8f43f-6343-4bb5-9568-0e5c84858e6f
-- title:
--   SNumbers: sn le approximation Number
-- statement:
--   For every `s`-number sequence and every operator `S : X → Y`,
--   `sₙ(S) ≤ aₙ(S)`: the approximation numbers are the largest `s`-numbers.
--   This is the easy half of Pietsch's sandwich theorem; it uses only axioms
--   (S2) and (S4) of `IsSNumberSequence`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L289-L299
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L289-L299

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

theorem SNumbers.sn_le_approximationNumber
    {s : Family 𝕜} (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ approximationNumber S n := by sorry
