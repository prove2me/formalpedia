-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:16:21.23821+00:00
-- url     : https://prove2.me/theorems/d2e9e491-3501-402e-a47c-f19e1589b173
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Chart comp one  39cc6a6ed057: P2 M Reciprocity Theory Chart Restriction G Chart comp one  39cc6a6ed057
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Chart comp one  39cc6a6ed057 construction uses the P2 M Reciprocity Theory Chart Restriction G Chart comp one  39cc6a6ed057 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftInjective.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftInjective.lean#L55-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_IsUnivChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057 {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Chart».«comp_one'» := P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
