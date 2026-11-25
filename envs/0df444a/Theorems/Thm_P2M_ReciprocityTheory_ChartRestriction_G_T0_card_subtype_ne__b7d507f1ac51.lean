-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_card_subtype_ne__b7d507f1ac51
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_card_subtype_ne__b7d507f1ac51
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:03.981471+00:00
-- url     : https://prove2.me/theorems/2db9f235-aefb-5c50-b419-3efcecd36be1
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 card subtype ne  b7d507f1ac51: P2 M Reciprocity Theory Chart Restriction G T0 card subtype ne  b7d507f1ac51
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 card subtype ne  b7d507f1ac51 construction uses the P2 M Reciprocity Theory Chart Restriction G T0 card subtype ne  b7d507f1ac51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValAlgebraMapEqZero.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValAlgebraMapEqZero.lean#L80-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_card_subtype_ne__b7d507f1ac51 {σ : Type} [Fintype σ] [DecidableEq σ] (e0 : σ) :
    Fintype.card {e // e ≠ e0} = Fintype.card σ - 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«card_subtype_ne'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_card_subtype_ne__b7d507f1ac51
