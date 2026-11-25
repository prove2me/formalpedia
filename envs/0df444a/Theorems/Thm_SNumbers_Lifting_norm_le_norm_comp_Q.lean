-- Prove2me | Theorems.Thm_SNumbers_Lifting_norm_le_norm_comp_Q
-- name    : SNumbers.Lifting.norm_le_norm_comp_Q
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:41:47.6886+00:00
-- url     : https://prove2.me/theorems/d4da6ff3-c6ae-5c95-83ee-d5ab8c9270aa
-- title:
--   Lifting: norm le norm comp Q
-- statement:
--   `‖B‖ ≤ ‖B ∘ Q‖`: the summation surjection `Q` sends the unit vector
--   `δ_x = lp.single 1 ⟨x,_⟩ 1` to `x`, so it hits every point of the closed unit
--   ball of `X`; composing with `Q` therefore cannot decrease the operator norm.
--   (The reverse `‖B ∘ Q‖ ≤ ‖B‖` is submultiplicativity with `‖Q‖ ≤ 1`.) The proof
--   reuses the density-of-norm scaling packaged in `exists_lift_of_pos_norm`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L240-L264
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L240-L264

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
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.Lifting.norm_le_norm_comp_Q {Z : Type u} [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (B : X →L[𝕜] Z) : ‖B‖ ≤ ‖B.comp (Q : BallLp 𝕜 X →L[𝕜] X)‖ := by sorry
