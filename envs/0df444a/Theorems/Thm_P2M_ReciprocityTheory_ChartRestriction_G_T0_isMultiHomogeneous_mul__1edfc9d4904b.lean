-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_isMultiHomogeneous_mul__1edfc9d4904b
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_isMultiHomogeneous_mul__1edfc9d4904b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:49:24.392804+00:00
-- url     : https://prove2.me/theorems/eb7d4587-e5ff-417f-a063-97b08cfeae89
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 is Multi Homogeneous mul  1edfc9d4904b: P2 M Reciprocity Theory Chart Restriction G T0 is Multi Homogeneous mul  1edfc9d4904b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 is Multi Homogeneous mul  1edfc9d4904b construction uses the P2 M Reciprocity Theory Chart Restriction G T0 is Multi Homogeneous mul  1edfc9d4904b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightProdPowMultiHomogeneous.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightProdPowMultiHomogeneous.lean#L8-L15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationGenericRatioEqRestriction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightProdPowMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField ReciprocityTheory.MultiplicativeHeights

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_isMultiHomogeneous_mul__1edfc9d4904b {R : Type*} [CommSemiring R] {B n : ℕ} {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin n) R} (hf : IsMultiHomogeneous a f)
    (hg : IsMultiHomogeneous a' g) : IsMultiHomogeneous (a + a') (f * g) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«isMultiHomogeneous_mul'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_isMultiHomogeneous_mul__1edfc9d4904b
