-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_card_finrankSubspaces_mul_frameProd
-- name    : SharpIntermediateSubgroupBounds.card_finrankSubspaces_mul_frameProd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:06.493028+00:00
-- url     : https://prove2.me/theorems/f0acd9a9-f65d-4a84-a746-e58fa24872d3
-- title:
--   Sharp Intermediate Subgroup Bounds: card finrank Subspaces mul frame Prod
-- statement:
--   Counting independent frames by their span.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L342-L366
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L342-L366

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators

theorem SharpIntermediateSubgroupBounds.card_finrankSubspaces_mul_frameProd
    {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V]
    [Finite V] {k : ℕ} (hk : k ≤ Module.finrank K V) :
    Nat.card (FinrankSubspaces K V k) * frameProd (Fintype.card K) k k =
      frameProd (Fintype.card K) (Module.finrank K V) k := by sorry
