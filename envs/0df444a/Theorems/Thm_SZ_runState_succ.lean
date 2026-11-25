-- Prove2me | Theorems.Thm_SZ_runState_succ
-- name    : SZ.runState_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:52:48.51259+00:00
-- url     : https://prove2.me/theorems/2b6f280b-fe83-46ab-b985-5f567fc7269f
-- title:
--   SZ: run State succ
-- statement:
--   The SZ construction uses the run State succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L96-L97
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L96-L97

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.runState_succ (s₀ : ℤ × ℤ) (d : ℕ → ℤ × ℤ) (k : ℕ) :
    runState s₀ d (k + 1) = stepS (runState s₀ d k) (d k) := by sorry
