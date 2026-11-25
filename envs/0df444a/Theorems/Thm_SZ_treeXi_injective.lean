-- Prove2me | Theorems.Thm_SZ_treeXi_injective
-- name    : SZ.treeXi_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:23:12.113582+00:00
-- url     : https://prove2.me/theorems/0ec42add-7ca9-4cb2-aca1-75398bcd329c
-- title:
--   SZ: tree Xi injective
-- statement:
--   The SZ construction uses the tree Xi injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1172-L1172
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1172-L1172

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.treeXi_injective : Function.Injective treeXi := by sorry
