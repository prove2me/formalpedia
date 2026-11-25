-- Prove2me | Theorems.Thm_SNumbers_hilbertSet_bddAbove
-- name    : SNumbers.hilbertSet_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:19:32.327915+00:00
-- url     : https://prove2.me/theorems/4d62b4b3-fd8f-4377-8af8-7c756dd95f46
-- title:
--   SNumbers: hilbert Set bdd Above
-- statement:
--   The SNumbers construction uses the hilbert Set bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L116-L117
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L116-L117

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

theorem SNumbers.hilbertSet_bddAbove (S : X →L[𝕜] Y) (n : ℕ) : BddAbove (hilbertSet S n) := by sorry
