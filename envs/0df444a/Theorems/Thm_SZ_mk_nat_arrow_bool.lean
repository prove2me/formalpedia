-- Prove2me | Theorems.Thm_SZ_mk_nat_arrow_bool
-- name    : SZ.mk_nat_arrow_bool
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:25:10.969653+00:00
-- url     : https://prove2.me/theorems/0f28eb86-0c7b-415b-8e6f-a1ed905f5c33
-- title:
--   SZ: mk nat arrow bool
-- statement:
--   The SZ construction uses the mk nat arrow bool property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1174-L1176
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1174-L1176

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.mk_nat_arrow_bool : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by sorry
