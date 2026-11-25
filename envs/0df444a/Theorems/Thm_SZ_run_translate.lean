-- Prove2me | Theorems.Thm_SZ_run_translate
-- name    : SZ.run_translate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:20:17.724425+00:00
-- url     : https://prove2.me/theorems/fec45ab1-a1c1-4ca1-ad9d-e55e2069c9b4
-- title:
--   SZ: run translate
-- statement:
--   **Every admissible play converges to a solution of the translate equation.**
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L870-L910
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L870-L910

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.run_translate {d : ℕ → ℤ × ℤ} (hrun : IsRun (-12, 9) d) :
    digitReal 3 (fun i => (d i).1) + Real.sqrt 3 * digitReal 3 (fun i => (d i).2)
      = 3 * Real.sqrt 3 - 4 := by sorry
