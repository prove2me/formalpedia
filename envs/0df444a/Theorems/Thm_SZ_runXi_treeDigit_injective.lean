-- Prove2me | Theorems.Thm_SZ_runXi_treeDigit_injective
-- name    : SZ.runXi_treeDigit_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:23:14.277842+00:00
-- url     : https://prove2.me/theorems/f5e6f937-4fa1-4efc-bf14-967cfa89c465
-- title:
--   SZ: run Xi tree Digit injective
-- statement:
--   **The tree is faithful**: different bit streams give different witnesses.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1121-L1154
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1121-L1154

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.runXi_treeDigit_injective :
    Function.Injective (fun β : ℕ → Bool => runXi (treeDigit β)) := by sorry
