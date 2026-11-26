-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_card_orderedBases_fin_zmod
-- name    : SharpIntermediateSubgroupBounds.card_orderedBases_fin_zmod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:46:58.877217+00:00
-- url     : https://prove2.me/theorems/1928fc20-bcd7-5944-a837-1902d34272e8
-- title:
--   Sharp Intermediate Subgroup Bounds: card ordered Bases fin zmod
-- statement:
--   The exact number of ordered bases of the standard `r`-space over
--   `ZMod p`, expressed as the ordered-frame product.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L334-L339
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/QBinomial.lean#L334-L339

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

theorem SharpIntermediateSubgroupBounds.card_orderedBases_fin_zmod (p r : ℕ) [Fact p.Prime] :
    Nat.card (LinearIndependentFrames (ZMod p) (Fin r → ZMod p) r) =
      frameProd p r r := by sorry
