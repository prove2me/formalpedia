-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_sqrt_mul_min
-- name    : SNumbers.approximationNumber_le_sqrt_mul_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:19:01.121245+00:00
-- url     : https://prove2.me/theorems/6f46f9b7-4368-464e-bca3-6e578eb0e5fa
-- title:
--   SNumbers: approximation Number le sqrt mul min
-- statement:
--   **Approximation vs. Gelfand and Kolmogorov numbers.** The combined
--   bound `aₙ(S) ≤ (1 + √n)·min(cₙ(S), dₙ(S))`: the largest `s`-number `aₙ`
--   exceeds neither `cₙ` nor `dₙ` by more than the factor `1 + √n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L575-L582
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L575-L582

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]

theorem SNumbers.approximationNumber_le_sqrt_mul_min (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤
      (1 + Real.sqrt n) * min (gelfandNumber S n) (kolmogorovNumber S n) := by sorry
