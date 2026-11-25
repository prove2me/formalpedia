-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__sub_69b16cdcbcca
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__sub_69b16cdcbcca
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:58.464157+00:00
-- url     : https://prove2.me/theorems/d4ec826a-ac9c-42af-afdd-a9066d2ad148
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Val At val At  sub 69b16cdcbcca: P2 M Reciprocity Theory Chart Restriction G TB Val At val At  sub 69b16cdcbcca
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Val At val At  sub 69b16cdcbcca construction uses the P2 M Reciprocity Theory Chart Restriction G TB Val At val At  sub 69b16cdcbcca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L33-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.ValAt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}}

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__sub_69b16cdcbcca (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f - g) = valAt' x U f - valAt' x U g := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«ValAt».«valAt'_sub» := P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__sub_69b16cdcbcca
