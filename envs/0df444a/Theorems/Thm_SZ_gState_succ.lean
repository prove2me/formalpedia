-- Prove2me | Theorems.Thm_SZ_gState_succ
-- name    : SZ.gState_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:52:52.893847+00:00
-- url     : https://prove2.me/theorems/8707a683-1116-4aeb-97a3-1401a05e10cf
-- title:
--   SZ: g State succ
-- statement:
--   The SZ construction uses the g State succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L152-L153
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L152-L153

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.gState_succ (s : ℤ × ℤ) (k : ℕ) :
    gState s (k + 1) = stepS (gState s k) (gDigit s k) := by sorry
