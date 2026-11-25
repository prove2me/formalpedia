-- Prove2me | Theorems.Thm_SZ_not_countable_witnessSet
-- name    : SZ.not_countable_witnessSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:23:04.092978+00:00
-- url     : https://prove2.me/theorems/9321a577-0417-57fa-a64a-d7ba74a3d4a5
-- title:
--   SZ: not countable witness Set
-- statement:
--   The SZ construction uses the not countable witness Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1197-L1201
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1197-L1201

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.not_countable_witnessSet : ¬ witnessSet.Countable := by sorry
