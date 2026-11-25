-- Prove2me | Theorems.Thm_SNumbers_isStrictSNumberSequence_approximationNumber
-- name    : SNumbers.isStrictSNumberSequence_approximationNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:56:12.472444+00:00
-- url     : https://prove2.me/theorems/2ff950ca-9f51-4177-8fd2-f889bc66a591
-- title:
--   SNumbers: is Strict SNumber Sequence approximation Number
-- statement:
--   Over a complete field, approximation numbers form a *strict* s-number
--   sequence: in addition to (S1)–(S5) they satisfy (S5'), the strong
--   normalisation `a_n (id_X) = 1` for every normed space `X` with `dim X > n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L407-L410
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L407-L410

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
variable [CompleteSpace 𝕜]

theorem SNumbers.isStrictSNumberSequence_approximationNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜) approxFamily := by sorry
