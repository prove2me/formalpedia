-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_sn
-- name    : SNumbers.approximationNumber_le_sn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:08:00.2058+00:00
-- url     : https://prove2.me/theorems/7eed67fa-ea01-4311-a242-badbd953f666
-- title:
--   SNumbers: approximation Number le sn
-- statement:
--   **Lower bound.** On Hilbert spaces, `aₙ(S) ≤ sₙ(S)` for every
--   `s`-number sequence `s`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Uniqueness.lean#L114-L124
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Uniqueness.lean#L114-L124

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

theorem SNumbers.approximationNumber_le_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    approximationNumber S n ≤ s S n := by sorry
