-- Prove2me | Theorems.Thm_SNumbers_Lifting_approx_le_kolmogorovNumber
-- name    : SNumbers.Lifting.approx_le_kolmogorovNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:54:57.103541+00:00
-- url     : https://prove2.me/theorems/26da6c3f-83e4-4627-8d14-cd4e38390ee5
-- title:
--   Lifting: approx le kolmogorov Number
-- statement:
--   **Pietsch's identity, `(≥)` half:** `aₙ(S ∘ Q) ≤ dₙ(S)`.
--
--   For an admissible subspace `V` and `ε > 0`, choose for each `x ∈ B_X` a point
--   `w x ∈ V` with `‖S x − w x‖ < ‖π_V ∘ S‖ + ε` (possible since
--   `‖[S x]‖ ≤ ‖π_V ∘ S‖`), and lift these to the rank-`≤ n` operator
--   `L α := ∑' x, α x • w x` (landing in the finite-dimensional, hence complete,
--   subspace `V`). Then `‖S∘Q − L‖ ≤ ‖π_V ∘ S‖ + ε`, so `aₙ(S∘Q) ≤ dₙ(S) + ε`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L603-L718
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L603-L718

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
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.Lifting.approx_le_kolmogorovNumber (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) n
      ≤ SNumbers.kolmogorovNumber S n := by sorry
