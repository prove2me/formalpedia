-- Prove2me | Theorems.Thm_SNumbers_isSNumberSequence_approximationNumber
-- name    : SNumbers.isSNumberSequence_approximationNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:33.871959+00:00
-- url     : https://prove2.me/theorems/efadfa72-229d-4f0b-957d-317b56bc95f0
-- title:
--   SNumbers: is SNumber Sequence approximation Number
-- statement:
--   Over a complete field, the approximation numbers form an s-number sequence in
--   the sense of Pietsch; (S5) comes from the strict normalisation.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L394-L402
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L394-L402

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

theorem SNumbers.isSNumberSequence_approximationNumber :
    IsSNumberSequence (𝕜 := 𝕜) approxFamily := by sorry
