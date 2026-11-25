-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_nonneg
-- name    : SNumbers.hilbertNumber_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:47:21.482476+00:00
-- url     : https://prove2.me/theorems/ff0dee25-5044-4b58-8369-670a65a3051a
-- title:
--   SNumbers: hilbert Number nonneg
-- statement:
--   The SNumbers construction uses the hilbert Number nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L127-L130
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L127-L130

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

theorem SNumbers.hilbertNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) : 0 ≤ hilbertNumber S n := by sorry
