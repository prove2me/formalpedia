-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualLift_comp_jetSub
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.dualLift_comp_jetSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:53.637695+00:00
-- url     : https://prove2.me/theorems/b04428d4-13d2-4e06-a73c-c39600c2bda1
-- title:
--   Chart: dual Lift comp jet Sub
-- statement:
--   The Chart construction uses the dual Lift comp jet Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L98-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L98-L106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
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

theorem ReciprocityTheory.ChartRestriction.G.Chart.dualLift_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (c : Fin a → R) :
    (dualLift c).comp (jetSub T 1) = dualLift (T c) := by sorry
