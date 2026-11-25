-- Prove2me | Theorems.Thm_SNumbers_ratio_le_norm
-- name    : SNumbers.ratio_le_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:40:32.198815+00:00
-- url     : https://prove2.me/theorems/8abebe8b-3ca8-4ec0-b752-3632ce8195e3
-- title:
--   SNumbers: ratio le norm
-- statement:
--   Every ratio `a_n (B S A)/(‖B‖‖A‖)` is `≤ ‖S‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L106-L114
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L106-L114

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

theorem SNumbers.ratio_le_norm (S : X →L[𝕜] Y) (n : ℕ) {A : L2 𝕜 →L[𝕜] X} {B : Y →L[𝕜] L2 𝕜}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖) ≤ ‖S‖ := by sorry
