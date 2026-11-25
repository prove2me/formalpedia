-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_sqrt_mul_kolmogorovNumber
-- name    : SNumbers.approximationNumber_le_sqrt_mul_kolmogorovNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:55:58.815283+00:00
-- url     : https://prove2.me/theorems/75db2f54-afe6-42fb-8c7b-1312596365b9
-- title:
--   SNumbers: approximation Number le sqrt mul kolmogorov Number
-- statement:
--   **Kolmogorov bound.** `aₙ(S) ≤ (1 + √n)·dₙ(S)` (Pietsch
--   [Pie87, 2.10.2]). The per-subspace bound is uniform over the
--   dimension-`≤ n` subspaces, so it passes to the infimum defining `dₙ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L561-L569
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L561-L569

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

theorem SNumbers.approximationNumber_le_sqrt_mul_kolmogorovNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * kolmogorovNumber S n := by sorry
