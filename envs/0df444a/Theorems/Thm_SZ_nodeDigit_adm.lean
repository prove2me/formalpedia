-- Prove2me | Theorems.Thm_SZ_nodeDigit_adm
-- name    : SZ.nodeDigit_adm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:39:22.609658+00:00
-- url     : https://prove2.me/theorems/6dd5f547-4986-4bd1-849a-1b8f4a22ed91
-- title:
--   SZ: node Digit adm
-- statement:
--   Whatever the node does, the offset it plays is admissible.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L650-L655
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L650-L655

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.nodeDigit_adm (β : ℕ → Bool) (n : Node) (h0 : 0 ≤ valS n.st)
    (h1 : valS n.st ≤ 3 + 3 * Real.sqrt 3) : Adm n.st (nodeDigit β n) := by sorry
