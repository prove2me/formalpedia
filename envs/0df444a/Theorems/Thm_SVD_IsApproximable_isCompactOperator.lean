-- Prove2me | Theorems.Thm_SVD_IsApproximable_isCompactOperator
-- name    : SVD.IsApproximable.isCompactOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:22:48.995116+00:00
-- url     : https://prove2.me/theorems/f3c363fb-e6b7-4d1f-b085-1c2dce8ed19f
-- title:
--   Is Approximable: is Compact Operator
-- statement:
--   **Approximable ⇒ compact.** Every operator approximable in operator
--   norm by finite-rank ones is compact:
--
--   * a finite-rank `Lₙ : X →L[𝕜] Y` factors as `(range Lₙ).subtypeL ∘ Lₙ'`
--     where `Lₙ' : X →L[𝕜] (range Lₙ)` lands in a finite-dimensional, hence
--     locally compact, subspace; hence `Lₙ` is compact
--     (`isCompactOperator_of_locallyCompactSpace_dom`);
--   * compactness is preserved under operator-norm limits
--     (`isCompactOperator_of_tendsto`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L331-L364
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L331-L364

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open Filter Topology
open SVD
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable [LocallyCompactSpace 𝕜] [CompleteSpace Y]

theorem SVD.IsApproximable.isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsApproximable S) : IsCompactOperator S := by sorry
