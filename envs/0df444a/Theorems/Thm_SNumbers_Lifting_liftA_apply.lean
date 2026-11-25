-- Prove2me | Theorems.Thm_SNumbers_Lifting_liftA_apply
-- name    : SNumbers.Lifting.liftA_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:39:22.100517+00:00
-- url     : https://prove2.me/theorems/75345b21-1f03-4e14-aef2-2ea881cd7afb
-- title:
--   Lifting: lift A apply
-- statement:
--   The lift applied to `α ∈ ℓ¹(B_W)` is the series `∑' w, α w • liftBasis w`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L390-L392
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L390-L392

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
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
omit [CompleteSpace W] [CompleteSpace X]

theorem SNumbers.Lifting.liftA_apply (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0)
    (α : BallLp 𝕜 W) :
    liftA A hc hc_ne α = ∑' w : Ball W, α w • liftBasis hc hc_ne w := by sorry

attribute [defeq] SNumbers.Lifting.liftA_apply
