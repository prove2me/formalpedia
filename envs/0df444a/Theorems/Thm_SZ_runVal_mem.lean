-- Prove2me | Theorems.Thm_SZ_runVal_mem
-- name    : SZ.runVal_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:14:39.192199+00:00
-- url     : https://prove2.me/theorems/f8e349e5-1b6d-5be6-8b13-f18e2f7c2c41
-- title:
--   SZ: run Val mem
-- statement:
--   **The invariant** along any play: the state never leaves `[0, 3U]`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L100-L108
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L100-L108

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.runVal_mem {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d)
    (h0 : 0 ≤ valS s₀) (h1 : valS s₀ ≤ 3 + 3 * Real.sqrt 3) (k : ℕ) :
    0 ≤ valS (runState s₀ d k) ∧ valS (runState s₀ d k) ≤ 3 + 3 * Real.sqrt 3 := by sorry
