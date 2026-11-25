-- Prove2me | Theorems.Thm_SNumbers_max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber
-- name    : SNumbers.max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:21:21.379652+00:00
-- url     : https://prove2.me/theorems/22f541f3-ba0d-4679-940a-13e5102e0004
-- title:
--   SNumbers: max gelfand Number kolmogorov Number le e mul hilbert Number
-- statement:
--   `max(cₙ(S), dₙ(S)) ≤ e·(n+1)·hₙ(S)`: the Gelfand and Kolmogorov numbers
--   exceed the smallest s-numbers `hₙ` by at most a factor linear in `n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L957-L962
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L957-L962

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n := by sorry
