-- Prove2me | Theorems.Thm_SZ_run_coupling
-- name    : SZ.run_coupling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:22:33.144573+00:00
-- url     : https://prove2.me/theorems/40eee980-3dd0-4b28-95c9-66d432e16f72
-- title:
--   SZ: run coupling
-- statement:
--   The coupling `u = 4 + x = √3 (2 + y)`, for every play.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L933-L938
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L933-L938

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.run_coupling {d : ℕ → ℤ × ℤ} (hrun : IsRun (-12, 9) d) :
    4 + digitReal 3 (fun i => (d i).1) = Real.sqrt 3 * (2 + digitReal 3 (runY d)) := by sorry
