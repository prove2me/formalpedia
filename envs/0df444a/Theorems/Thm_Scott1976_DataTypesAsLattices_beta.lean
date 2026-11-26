-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_beta
-- name    : Scott1976.DataTypesAsLattices.beta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:27.218986+00:00
-- url     : https://prove2.me/theorems/cc874704-3600-495c-94a0-c10eadf41d09
-- title:
--   Data Types As Lattices: beta
-- statement:
--   **Scott 1976, (β) for continuous `τ`.** `(λ x. τ)(y) = τ[y/x]`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L122-L124
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L122-L124

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.beta {τ : Pomega → Pomega} (hτ : IsScottContinuous τ) (y : Pomega) :
    funOf (lam τ) y = τ y := by sorry
