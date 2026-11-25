-- Prove2me | Theorems.Thm_SVD_isCompactOperator_of_rank_le
-- name    : SVD.isCompactOperator_of_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:56:18.872946+00:00
-- url     : https://prove2.me/theorems/3421d8cf-ba0b-41d5-9407-09982a633352
-- title:
--   SVD: is Compact Operator of rank le
-- statement:
--   **Finite rank ⇒ compact.** An operator of rank at most `m` is approximable
--   (`IsApproximable.of_rank_le`), hence compact.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L368-L370
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L368-L370

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

theorem SVD.isCompactOperator_of_rank_le {S : X →L[𝕜] Y} {m : ℕ}
    (hS : S.rank ≤ (m : Cardinal)) : IsCompactOperator S := by sorry
