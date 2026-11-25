-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetSub_comp
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jetSub_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:30.268143+00:00
-- url     : https://prove2.me/theorems/e07bf86e-8132-5a74-accd-275179ac276d
-- title:
--   Chart: jet Sub comp
-- statement:
--   The Chart construction uses the jet Sub comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L52-L63

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.jetSub_comp {a b c : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (S : (Fin c → R) →ₗ[R] (Fin a → R)) (m : ℕ) :
    (jetSub S m).comp (jetSub T m) = jetSub (T.comp S) m := by sorry
