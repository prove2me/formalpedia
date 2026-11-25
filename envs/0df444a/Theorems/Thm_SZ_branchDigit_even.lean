-- Prove2me | Theorems.Thm_SZ_branchDigit_even
-- name    : SZ.branchDigit_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:17:28.405888+00:00
-- url     : https://prove2.me/theorems/ff0afbb9-e2c3-5ba2-bdd2-2473abf82781
-- title:
--   SZ: branch Digit even
-- statement:
--   The SZ construction uses the branch Digit even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L562-L563
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L562-L563

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.branchDigit_even (w : ℝ) (b : Bool) : EvenDigit (branchDigit w b) := by sorry
