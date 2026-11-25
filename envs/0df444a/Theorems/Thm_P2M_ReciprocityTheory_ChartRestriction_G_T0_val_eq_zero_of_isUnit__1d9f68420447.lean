-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_val_eq_zero_of_isUnit__1d9f68420447
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_val_eq_zero_of_isUnit__1d9f68420447
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:02.826562+00:00
-- url     : https://prove2.me/theorems/5489c9b3-e6d1-5a24-956a-f24bc287fa51
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 val eq zero of is Unit  1d9f68420447: P2 M Reciprocity Theory Chart Restriction G T0 val eq zero of is Unit  1d9f68420447
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 val eq zero of is Unit  1d9f68420447 construction uses the P2 M Reciprocity Theory Chart Restriction G T0 val eq zero of is Unit  1d9f68420447 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L214-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraicIndependentResidueOfIsUnit.lean#L214-L224

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_val_eq_zero_of_isUnit__1d9f68420447 {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {z : E}
    (h : z ∈ vRing v) (hu : IsUnit (⟨z, h⟩ : vRing v)) : v z = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«val_eq_zero_of_isUnit'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_val_eq_zero_of_isUnit__1d9f68420447
