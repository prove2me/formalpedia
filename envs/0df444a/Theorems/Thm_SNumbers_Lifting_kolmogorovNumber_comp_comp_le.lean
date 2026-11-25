-- Prove2me | Theorems.Thm_SNumbers_Lifting_kolmogorovNumber_comp_comp_le
-- name    : SNumbers.Lifting.kolmogorovNumber_comp_comp_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:12:45.384829+00:00
-- url     : https://prove2.me/theorems/48ae0a6b-b6fd-4552-bb32-5dd3bda23ead
-- title:
--   Lifting: kolmogorov Number comp comp le
-- statement:
--   (S3) Ideal property.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L414-L450
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L414-L450

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_kolmogorovNumber_comp_comp_le

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.Lifting.kolmogorovNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber S n * ‖A‖ := by sorry
