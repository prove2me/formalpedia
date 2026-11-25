-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_two_mul_entropyNumber
-- name    : SNumbers.approximationNumber_le_two_mul_entropyNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:09:46.436897+00:00
-- url     : https://prove2.me/theorems/1ec53236-afa7-5dbe-b907-b95e5af48374
-- title:
--   SNumbers: approximation Number le two mul entropy Number
-- statement:
--   **`aₙ(T) ≤ 2·eₙ(T)` between Hilbert spaces.** For `γ < aₙ(T)` the scalar
--   factorisation gives contractions with `B ∘ T ∘ A = γ · id` on `ℓ₂ⁿ⁺¹`; rescaling
--   `B` by `γ⁻¹` makes the composition the identity, so
--   `1/2 ≤ eₙ(id) ≤ γ⁻¹ · eₙ(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L935-L974
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L935-L974

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
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

theorem SNumbers.approximationNumber_le_two_mul_entropyNumber (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    approximationNumber T n ≤ 2 * entropyNumber T n := by sorry
