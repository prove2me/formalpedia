-- Prove2me | Theorems.Thm_SVD_IsApproximable_comp_left
-- name    : SVD.IsApproximable.comp_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:27:32.10222+00:00
-- url     : https://prove2.me/theorems/00ec2ce4-ae0b-536b-8c8e-0cfa09466652
-- title:
--   Is Approximable: comp left
-- statement:
--   The Is Approximable construction uses the comp left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L298-L303
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L298-L303

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

theorem SVD.IsApproximable.comp_left {S : X →L[𝕜] Y}
    (B : Y →L[𝕜] Z) (hS : IsApproximable S) :
    IsApproximable (B.comp S) := by sorry
