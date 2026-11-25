-- Prove2me | Theorems.Thm_SVD_IsApproximable_of_rank_le
-- name    : SVD.IsApproximable.of_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:22:28.246849+00:00
-- url     : https://prove2.me/theorems/806ec1df-362d-4bfd-a8f4-b35d98057c46
-- title:
--   Is Approximable: of rank le
-- statement:
--   Every finite-rank continuous linear map is approximable: by (S4),
--   `aₙ(S) = 0` for all `n ≥ rank S`, hence `aₙ(S) → 0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L113-L121
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L113-L121

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

theorem SVD.IsApproximable.of_rank_le {S : X →L[𝕜] Y} {N : ℕ}
    (hS : S.rank ≤ (N : Cardinal)) : IsApproximable S := by sorry
