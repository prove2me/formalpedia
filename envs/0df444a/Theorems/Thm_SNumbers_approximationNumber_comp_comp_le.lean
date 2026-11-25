-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_comp_comp_le
-- name    : SNumbers.approximationNumber_comp_comp_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:57:23.553477+00:00
-- url     : https://prove2.me/theorems/8b5c0c2f-a0e5-4a8f-ac4c-a9b7cd15f928
-- title:
--   SNumbers: approximation Number comp comp le
-- statement:
--   **(S3) Ideal property.** `a_n (B ∘ S ∘ A) ≤ ‖B‖ * a_n S * ‖A‖`: multiplicativity
--   applied twice with one index `0`, since `a_0 = ‖·‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L265-L280
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L265-L280

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

theorem SNumbers.approximationNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    approximationNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * approximationNumber S n * ‖A‖ := by sorry
