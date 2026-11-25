-- Prove2me | Theorems.Thm_SVD_IsApproximable_comp_comp
-- name    : SVD.IsApproximable.comp_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:22:44.3316+00:00
-- url     : https://prove2.me/theorems/eaa92faf-c790-46a6-9fc6-82068848b462
-- title:
--   Is Approximable: comp comp
-- statement:
--   Pre/post-composition with bounded operators preserves approximability:
--   this is the *ideal property* for the class of approximable operators,
--   inherited from the (S3) ideal property of the approximation numbers.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L282-L296
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L282-L296

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

theorem SVD.IsApproximable.comp_comp {S : X →L[𝕜] Y}
    (A : W →L[𝕜] X) (B : Y →L[𝕜] Z) (hS : IsApproximable S) :
    IsApproximable (B.comp (S.comp A)) := by sorry
