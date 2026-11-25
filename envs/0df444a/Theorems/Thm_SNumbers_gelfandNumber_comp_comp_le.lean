-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_comp_comp_le
-- name    : SNumbers.gelfandNumber_comp_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:11.45724+00:00
-- url     : https://prove2.me/theorems/9a7e1935-4100-4c4f-9ae0-fa6afcc7c6ea
-- title:
--   SNumbers: gelfand Number comp comp le
-- statement:
--   (S3) `c_n (B ∘ S ∘ A) ≤ ‖B‖ * c_n S * ‖A‖`: multiplicativity applied twice with one
--   index `0`, since `c_0 = ‖·‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L406-L419
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L406-L419

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
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

theorem SNumbers.gelfandNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    gelfandNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * gelfandNumber S n * ‖A‖ := by sorry
