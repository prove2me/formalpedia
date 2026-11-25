-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_antitone
-- name    : SNumbers.hilbertNumber_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:40:46.757244+00:00
-- url     : https://prove2.me/theorems/28724fe2-b426-4321-9e5d-668c3f4c4041
-- title:
--   SNumbers: hilbert Number antitone
-- statement:
--   (S1b) `h_{n+1} S ≤ h_n S`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L133-L140
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L133-L140

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

theorem SNumbers.hilbertNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S (n + 1) ≤ hilbertNumber S n := by sorry
