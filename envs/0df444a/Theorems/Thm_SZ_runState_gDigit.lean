-- Prove2me | Theorems.Thm_SZ_runState_gDigit
-- name    : SZ.runState_gDigit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:48.283814+00:00
-- url     : https://prove2.me/theorems/814edc5a-35e5-40bc-892e-95e8479cabd7
-- title:
--   SZ: run State g Digit
-- statement:
--   The SZ construction uses the run State g Digit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L185-L188
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L185-L188

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.runState_gDigit (s : ℤ × ℤ) (k : ℕ) : runState s (gDigit s) k = gState s k := by sorry
