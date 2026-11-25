-- Prove2me | Theorems.Thm_SVD_isApproximable_iff_isCompactOperator
-- name    : SVD.isApproximable_iff_isCompactOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:12:32.697799+00:00
-- url     : https://prove2.me/theorems/b07d72d1-fb75-44a2-b9db-8fcc99cd29b1
-- title:
--   SVD: is Approximable iff is Compact Operator
-- statement:
--   On Hilbert spaces, approximable and compact operators coincide.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L440-L442
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L440-L442

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

theorem SVD.isApproximable_iff_isCompactOperator (S : H₁ →L[𝕜] H₂) :
    IsApproximable S ↔ IsCompactOperator S := by sorry
