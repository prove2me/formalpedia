-- Prove2me | Theorems.Thm_SNumbers_le_sn_of_lt_approximationNumber
-- name    : SNumbers.le_sn_of_lt_approximationNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:12:12.7388+00:00
-- url     : https://prove2.me/theorems/dde2c6d3-771a-4a86-a66d-5be186900ab9
-- title:
--   SNumbers: le sn of lt approximation Number
-- statement:
--   For every real `c` with `0 ≤ c < aₙ(S)`, every `s`-number sequence
--   satisfies `c ≤ sₙ(S)`. This is the core of the Hilbert-space lower bound;
--   it consumes the SVD factorisation `B ∘ S ∘ A = c • id`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Uniqueness.lean#L80-L110
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Uniqueness.lean#L80-L110

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_Uniqueness
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

theorem SNumbers.le_sn_of_lt_approximationNumber {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hca : c < approximationNumber S n) : c ≤ s S n := by sorry
