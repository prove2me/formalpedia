-- Prove2me | Theorems.Thm_SZ_gVal_succ
-- name    : SZ.gVal_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:12:42.817062+00:00
-- url     : https://prove2.me/theorems/4b6c5e1f-0e1d-49d2-ae24-e7402047104c
-- title:
--   SZ: g Val succ
-- statement:
--   The value of the rule's state at step `k + 1`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L234-L238
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L234-L238

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.gVal_succ (s : ℤ × ℤ) (k : ℕ) :
    valS (gState s (k + 1)) = 3 * (valS (gState s k)
      - (((pick (valS (gState s k))).1 : ℝ)
          + ((pick (valS (gState s k))).2 : ℝ) * Real.sqrt 3)) := by sorry
