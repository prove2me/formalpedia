-- Prove2me | Theorems.Thm_SZ_run_even_floor
-- name    : SZ.run_even_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:21:04.102704+00:00
-- url     : https://prove2.me/theorems/317d91bf-007d-54eb-b5d7-07f7db627ae7
-- title:
--   SZ: run even floor
-- statement:
--   **Every hygienic play is a witness for `√3`.**  The two hypotheses are lemma L1.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L950-L983
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L950-L983

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.run_even_floor {d : ℕ → ℤ × ℤ} (hrun : IsRun (-12, 9) d)
    (hA : ∀ N, ∃ k, N ≤ k ∧ (d k).1 = 0) (hB : ∀ N, ∃ k, N ≤ k ∧ (d k).2 = 2)
    {n : ℕ} (hn : 1 ≤ n) : Even ⌊runXi d * Real.sqrt 3 ^ n⌋ := by sorry
