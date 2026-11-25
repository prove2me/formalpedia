-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_def
-- name    : SNumbers.hilbertNumber_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:56:29.906874+00:00
-- url     : https://prove2.me/theorems/ea3c8c70-1ba1-4a2c-ad3e-ea4bcebd6946
-- title:
--   SNumbers: hilbert Number def
-- statement:
--   The SNumbers construction uses the hilbert Number def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L87-L88
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L87-L88

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

theorem SNumbers.hilbertNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n = sSup (hilbertSet S n) := by sorry
