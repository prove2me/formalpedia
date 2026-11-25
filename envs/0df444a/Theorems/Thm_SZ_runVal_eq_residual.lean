-- Prove2me | Theorems.Thm_SZ_runVal_eq_residual
-- name    : SZ.runVal_eq_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:19:36.174045+00:00
-- url     : https://prove2.me/theorems/30a2d826-cb78-5c08-887b-d225d2db64da
-- title:
--   SZ: run Val eq residual
-- statement:
--   The SZ construction uses the run Val eq residual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L838-L855
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L838-L855

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.runVal_eq_residual (d : ℕ → ℤ × ℤ) (k : ℕ) :
    valS (runState (-12, 9) d k) = 3 ^ (k + 1) * ((3 * Real.sqrt 3 - 4)
      - digitSum 3 (fun i => (d i).1) k
      - Real.sqrt 3 * digitSum 3 (fun i => (d i).2) k) := by sorry
