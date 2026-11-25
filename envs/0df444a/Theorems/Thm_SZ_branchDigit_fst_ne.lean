-- Prove2me | Theorems.Thm_SZ_branchDigit_fst_ne
-- name    : SZ.branchDigit_fst_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:23.123491+00:00
-- url     : https://prove2.me/theorems/592349a1-eaa3-59dd-9913-fb688130c3d3
-- title:
--   SZ: branch Digit fst ne
-- statement:
--   The SZ construction uses the branch Digit fst ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L557-L560
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L557-L560

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.branchDigit_fst_ne {w w' : ℝ} {b b' : Bool} (hb : b ≠ b') :
    (branchDigit w b).1 ≠ (branchDigit w' b').1 := by sorry
