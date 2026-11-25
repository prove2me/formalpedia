-- Prove2me | Theorems.Thm_SNumbers_Lifting_kolmogorovNumber_zero_eq_norm
-- name    : SNumbers.Lifting.kolmogorovNumber_zero_eq_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:11:41.782319+00:00
-- url     : https://prove2.me/theorems/8dec7bf7-5d55-47fd-9f89-42847bfeb884
-- title:
--   Lifting: kolmogorov Number zero eq norm
-- statement:
--   (S1a) `kolmogorovNumber S 0 = ‖S‖`. The lower bound `‖S‖ ≤ ‖S∘Q‖` is
--   `norm_le_norm_comp_Q`; the upper bound is submultiplicativity with `‖Q‖ ≤ 1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L268-L274
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L268-L274

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_kolmogorovNumber_zero_eq_norm

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
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.Lifting.kolmogorovNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    kolmogorovNumber S 0 = ‖S‖ := by sorry
