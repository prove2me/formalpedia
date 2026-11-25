-- Prove2me | Theorems.Thm_SNumbers_ratio_le_hilbertNumber
-- name    : SNumbers.ratio_le_hilbertNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:01:18.991448+00:00
-- url     : https://prove2.me/theorems/aa577dce-1bac-43a8-978e-826f83891f7c
-- title:
--   SNumbers: ratio le hilbert Number
-- statement:
--   Each admissible ratio is `≤ h_n S`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L120-L123
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L120-L123

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

theorem SNumbers.ratio_le_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) {A : L2 𝕜 →L[𝕜] X} {B : Y →L[𝕜] L2 𝕜}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖) ≤ hilbertNumber S n := by sorry
