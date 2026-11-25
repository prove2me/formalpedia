-- Prove2me | Theorems.Thm_SVD_IsApproximable_comp_right
-- name    : SVD.IsApproximable.comp_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:27:56.422695+00:00
-- url     : https://prove2.me/theorems/ab89811f-8c3e-4b77-a2d2-d61d4be3e073
-- title:
--   Is Approximable: comp right
-- statement:
--   The Is Approximable construction uses the comp right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L305-L310
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Approximable.lean#L305-L310

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

theorem SVD.IsApproximable.comp_right {S : X →L[𝕜] Y}
    (A : W →L[𝕜] X) (hS : IsApproximable S) :
    IsApproximable (S.comp A) := by sorry
