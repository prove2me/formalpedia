-- Prove2me | Theorems.Thm_SNumbers_sum_le_sqrt_card_mul_sqrt_sum_sq
-- name    : SNumbers.sum_le_sqrt_card_mul_sqrt_sum_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:21:41.010743+00:00
-- url     : https://prove2.me/theorems/1e9e0565-5fbc-40ee-8901-d087d02938d2
-- title:
--   SNumbers: sum le sqrt card mul sqrt sum sq
-- statement:
--   **Cauchy–Schwarz against the constant vector `1`:** a sum of reals is bounded
--   by `√(#ι)` times the `ℓ₂` norm of its terms. No sign assumption on `a` is needed.
--
--   This is the specialisation of Mathlib's two-sequence
--   `Real.sum_mul_le_sqrt_mul_sqrt` at `g ≡ 1`, which Mathlib itself does not
--   provide; it is used wherever a `∑ ‖·‖` has to be traded for a `√(∑ ‖·‖²)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L162-L165
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L162-L165

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

theorem SNumbers.sum_le_sqrt_card_mul_sqrt_sum_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∑ i, a i ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, a i ^ 2) := by sorry
