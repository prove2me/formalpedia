-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_le_sqrt_mul_bernsteinNumber_hilbert
-- name    : SNumbers.gelfandNumber_le_sqrt_mul_bernsteinNumber_hilbert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:17:55.332612+00:00
-- url     : https://prove2.me/theorems/ec8a2b85-ddc1-4df3-b6c8-160a45b2bca9
-- title:
--   SNumbers: gelfand Number le sqrt mul bernstein Number hilbert
-- statement:
--   **Reverse bound, Hilbert codomain.** If `H` is a Hilbert space then
--   `cₙ(S) ≤ √(n+1)·bₙ(S)`, sharp polynomial, product-free and pointwise (Theorem 8 of
--   [KNU25]). Orthonormal images give `‖S x‖² = ∑ ‖gⱼ‖²` (Parseval) and
--   `∑‖gⱼ‖ ≤ √(n+1)·‖S x‖` (Cauchy–Schwarz).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L286-L369
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L286-L369

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
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem SNumbers.gelfandNumber_le_sqrt_mul_bernsteinNumber_hilbert
    (S : X →L[𝕜] H) (n : ℕ) :
    gelfandNumber S n ≤ Real.sqrt ((n : ℝ) + 1) * bernsteinNumber S n := by sorry
