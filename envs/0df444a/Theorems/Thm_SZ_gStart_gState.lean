-- Prove2me | Theorems.Thm_SZ_gStart_gState
-- name    : SZ.gStart_gState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:15:18.456379+00:00
-- url     : https://prove2.me/theorems/87ebf29e-2ada-4644-b7ff-e1953a7d8472
-- title:
--   SZ: g Start g State
-- statement:
--   A reached state is again a legitimate start: this is what lets the tree recurse.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L202-L208
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L202-L208

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.gStart_gState {s : ℤ × ℤ} (h : GStart s) (N : ℕ) : GStart (gState s N) := by sorry
