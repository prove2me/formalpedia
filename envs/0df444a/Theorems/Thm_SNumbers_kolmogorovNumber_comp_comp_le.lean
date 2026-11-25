-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_comp_comp_le
-- name    : SNumbers.kolmogorovNumber_comp_comp_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:30:36.90349+00:00
-- url     : https://prove2.me/theorems/ab4c67b1-0063-4da4-817a-e222c49fb0c1
-- title:
--   SNumbers: kolmogorov Number comp comp le
-- statement:
--   (S3) `d_n (B ∘ S ∘ A) ≤ ‖B‖ * d_n S * ‖A‖`: multiplicativity applied twice with one
--   index `0`, since `d_0 = ‖·‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L388-L403
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L388-L403

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
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

theorem SNumbers.kolmogorovNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber S n * ‖A‖ := by sorry
