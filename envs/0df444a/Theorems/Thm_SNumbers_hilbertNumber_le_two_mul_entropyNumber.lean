-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_le_two_mul_entropyNumber
-- name    : SNumbers.hilbertNumber_le_two_mul_entropyNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:09:51.800629+00:00
-- url     : https://prove2.me/theorems/340d9376-b452-452b-8984-46eab7a3186f
-- title:
--   SNumbers: hilbert Number le two mul entropy Number
-- statement:
--   **The Hilbert-entropy bound** `hₙ(S) ≤ 2·eₙ(S)`, for operators between
--   arbitrary normed spaces. Every factorisation `B ∘ S ∘ A` over `ℓ₂` satisfies
--   `aₙ(B∘S∘A) ≤ 2·eₙ(B∘S∘A) ≤ 2·‖B‖·eₙ(S)·‖A‖`, and `hₙ` is the supremum of
--   `aₙ(B∘S∘A)/(‖B‖‖A‖)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L982-L995
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L982-L995

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.hilbertNumber_le_two_mul_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ 2 * entropyNumber S n := by sorry
