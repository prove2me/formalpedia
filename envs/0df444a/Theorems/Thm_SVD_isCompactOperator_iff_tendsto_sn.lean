-- Prove2me | Theorems.Thm_SVD_isCompactOperator_iff_tendsto_sn
-- name    : SVD.isCompactOperator_iff_tendsto_sn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:51:38.605864+00:00
-- url     : https://prove2.me/theorems/4f39f83e-8f45-47b0-a8d9-613993e04805
-- title:
--   SVD: is Compact Operator iff tendsto sn
-- statement:
--   **On Hilbert spaces every `s`-number sequence detects compactness.** All
--   `s`-number sequences agree with the approximation numbers there
--   (`SNumbers.allSNumbers_eq_on_HilbertSpace`), and `aₙ(S) → 0` is equivalent to
--   compactness by `isApproximable_iff_isCompactOperator`.
--
--   This fails on general Banach spaces for `s = aₙ` (Enflo), which is why the
--   Gelfand and Kolmogorov criteria in `SNumbers` are the ones stated there.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L451-L456
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L451-L456

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

theorem SVD.isCompactOperator_iff_tendsto_sn {s : SNumbers.Family 𝕜}
    (hs : SNumbers.IsSNumberSequence s) (S : H₁ →L[𝕜] H₂) :
    IsCompactOperator S ↔ Tendsto (fun n => s S n) atTop (𝓝 0) := by sorry
