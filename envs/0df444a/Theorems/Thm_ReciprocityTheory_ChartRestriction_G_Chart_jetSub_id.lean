-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetSub_id
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jetSub_id
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:57.315967+00:00
-- url     : https://prove2.me/theorems/3d100380-87f7-4e1f-8416-7c04bc5cf0e4
-- title:
--   Chart: jet Sub id
-- statement:
--   The Chart construction uses the jet Sub id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L46-L50

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.jetSub_id {a : ℕ} (m : ℕ) : jetSub (R := R) (LinearMap.id : (Fin a → R) →ₗ[R] (Fin a → R)) m = AlgHom.id R _ := by sorry
