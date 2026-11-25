-- Prove2me | Theorems.Thm_SVD_IsCompactOperator_isApproximable
-- name    : SVD.IsCompactOperator.isApproximable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:12:49.330833+00:00
-- url     : https://prove2.me/theorems/4ae93a1b-2849-55e5-912f-628211374319
-- title:
--   Is Compact Operator: is Approximable
-- statement:
--   On Hilbert spaces, every compact operator is approximable. The singular
--   value decomposition `IsCompactOperator.SVD` produces singular values `σₙ → 0`
--   which, by Eckart–Young (`svd_sigma_eq_approx`), equal the approximation numbers
--   `aₙ(S)`; hence `aₙ(S) → 0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L432-L437
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L432-L437

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

theorem SVD.IsCompactOperator.isApproximable {S : H₁ →L[𝕜] H₂}
    (hS : IsCompactOperator S) :
    IsApproximable S := by sorry
