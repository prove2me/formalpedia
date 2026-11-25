-- Prove2me | Theorems.Thm_SNumbers_allSNumbers_eq_on_HilbertSpace
-- name    : SNumbers.allSNumbers_eq_on_HilbertSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:07:19.836067+00:00
-- url     : https://prove2.me/theorems/9f6bc7d3-1e25-4cc2-a592-261976adfdf7
-- title:
--   SNumbers: all SNumbers eq on Hilbert Space
-- statement:
--   **Uniqueness theorem (Pietsch 2.11.9).** On Hilbert spaces, every
--   `s`-number sequence agrees with the approximation numbers:
--   `sₙ(S) = aₙ(S)`.
--
--   The upper bound is `sn_le_approximationNumber` (valid on any Banach space);
--   the lower bound is `approximationNumber_le_sn` (Hilbert-space SVD).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Uniqueness.lean#L132-L135
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Uniqueness.lean#L132-L135

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

theorem SNumbers.allSNumbers_eq_on_HilbertSpace {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    s S n = approximationNumber S n := by sorry
