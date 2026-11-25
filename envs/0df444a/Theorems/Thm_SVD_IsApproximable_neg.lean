-- Prove2me | Theorems.Thm_SVD_IsApproximable_neg
-- name    : SVD.IsApproximable.neg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:27:26.126183+00:00
-- url     : https://prove2.me/theorems/a901717b-08d4-4257-9b2a-3c6af85177e7
-- title:
--   Is Approximable: neg
-- statement:
--   Negation preserves approximability, as the special case `c = -1` of
--   `IsApproximable.smul`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L182-L185
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L182-L185

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

theorem SVD.IsApproximable.neg {S : X →L[𝕜] Y} (hS : IsApproximable S) :
    IsApproximable (-S) := by sorry
