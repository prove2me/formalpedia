-- Prove2me | Theorems.Thm_SNumbers_isSNumberSequence_hilbertNumber
-- name    : SNumbers.isSNumberSequence_hilbertNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:09.290902+00:00
-- url     : https://prove2.me/theorems/8a70ad58-7b51-457c-901a-7328cb291a88
-- title:
--   SNumbers: is SNumber Sequence hilbert Number
-- statement:
--   The Hilbert numbers form an s-number sequence. The axioms (S1)–(S4) are
--   the lemmas above; (S1a≥) and (S5) are `norm_le_hilbertNumber_zero` and
--   `one_le_hilbertNumber_id`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L411-L420
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L411-L420

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.isSNumberSequence_hilbertNumber :
    IsSNumberSequence (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => hilbertNumber S n) := by sorry
