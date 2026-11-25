-- Prove2me | Theorems.Thm_SVD_isCompactOperator_iff_tendsto_hilbertNumber
-- name    : SVD.isCompactOperator_iff_tendsto_hilbertNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:24:41.966912+00:00
-- url     : https://prove2.me/theorems/4a94827a-3947-5633-96cd-6910d4a0411f
-- title:
--   SVD: is Compact Operator iff tendsto hilbert Number
-- statement:
--   Hilbert-space case: compactness is equivalent to `hₙ(S) → 0`, even though
--   the Hilbert numbers are the *smallest* `s`-number sequence.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L466-L468
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L466-L468

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SVD
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

theorem SVD.isCompactOperator_iff_tendsto_hilbertNumber (S : H₁ →L[𝕜] H₂) :
    IsCompactOperator S ↔ Tendsto (SNumbers.hilbertNumber S) atTop (𝓝 0) := by sorry
