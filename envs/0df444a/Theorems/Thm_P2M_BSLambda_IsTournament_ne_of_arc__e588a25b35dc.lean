-- Prove2me | Theorems.Thm_P2M_BSLambda_IsTournament_ne_of_arc__e588a25b35dc
-- name    : P2M_BSLambda_IsTournament_ne_of_arc__e588a25b35dc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:08.963673+00:00
-- url     : https://prove2.me/theorems/9913cacd-5dc5-4d41-bda2-eb1bb9aac5f1
-- title:
--   P2 M BSLambda Is Tournament ne of arc  e588a25b35dc: P2 M BSLambda Is Tournament ne of arc  e588a25b35dc
-- statement:
--   The endpoints of an arc are distinct.  The primed name follows Mathlib's `LT.lt.ne'`
--   convention: the conclusion is `j ≠ i`, the reverse of `BSLambda.IsTournament.ne_of_arc`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L71-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L71-L71

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
open BSLambda.IsTournament
variable {Arc : ι → ι → Bool} (h : IsTournament Arc) {i j : ι}
include h

theorem P2M_BSLambda_IsTournament_ne_of_arc__e588a25b35dc (hij : Arc i j) : j ≠ i := by sorry

alias «BSLambda».«IsTournament».«ne_of_arc'» := P2M_BSLambda_IsTournament_ne_of_arc__e588a25b35dc
