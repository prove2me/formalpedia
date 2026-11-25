-- Prove2me | Theorems.Thm_SVD_IsApproximable_smul
-- name    : SVD.IsApproximable.smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:56:20.311577+00:00
-- url     : https://prove2.me/theorems/28f6489c-ec76-41fd-8cff-ac87e13c0ff5
-- title:
--   Is Approximable: smul
-- statement:
--   Scaling by a constant preserves approximability. The bound
--   `aₙ(c • S) ≤ ‖c‖ · aₙ(S)` follows from the per-approximant inequality
--   `‖c • S - c • L‖ = ‖c‖ · ‖S - L‖`, taken to the infimum over rank-`≤ n`
--   approximants `L`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L133-L178
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L133-L178

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

theorem SVD.IsApproximable.smul (c : 𝕜) {S : X →L[𝕜] Y}
    (hS : IsApproximable S) :
    IsApproximable (c • S) := by sorry
