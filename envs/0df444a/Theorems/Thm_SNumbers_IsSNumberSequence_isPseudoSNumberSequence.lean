-- Prove2me | Theorems.Thm_SNumbers_IsSNumberSequence_isPseudoSNumberSequence
-- name    : SNumbers.IsSNumberSequence.isPseudoSNumberSequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:26:43.4207+00:00
-- url     : https://prove2.me/theorems/6c8b3d55-c7e2-422b-8669-266f746e693b
-- title:
--   Is SNumber Sequence: is Pseudo SNumber Sequence
-- statement:
--   Every s-number sequence is a pseudo-s-number sequence.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L250-L252
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L250-L252

module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Definitions.Def_SNumbers_Basic
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

theorem SNumbers.IsSNumberSequence.isPseudoSNumberSequence {s : Family 𝕜} (h : IsSNumberSequence s) :
    IsPseudoSNumberSequence s := by sorry
