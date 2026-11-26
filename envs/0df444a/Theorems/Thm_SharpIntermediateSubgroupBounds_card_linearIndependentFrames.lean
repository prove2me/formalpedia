-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_card_linearIndependentFrames
-- name    : SharpIntermediateSubgroupBounds.card_linearIndependentFrames
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:56.462852+00:00
-- url     : https://prove2.me/theorems/8ed25edf-b300-5ce8-ac86-a4d898415f6b
-- title:
--   Sharp Intermediate Subgroup Bounds: card linear Independent Frames
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the card linear Independent Frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L325-L330
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L325-L330

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

theorem SharpIntermediateSubgroupBounds.card_linearIndependentFrames
    {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V]
    [Finite V] {k : ℕ} (hk : k ≤ Module.finrank K V) :
    Nat.card (LinearIndependentFrames K V k) =
      frameProd (Fintype.card K) (Module.finrank K V) k := by sorry
