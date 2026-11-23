-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetSub_zR
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jetSub_zR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:16.078106+00:00
-- url     : https://prove2.me/theorems/c3065ede-a977-4bad-940e-c353772bdd48
-- title:
--   Chart: jet Sub z R
-- statement:
--   The Chart construction uses the jet Sub z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L35-L37

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.jetSub_zR {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) (k : Fin b) :
    jetSub T m (zR m k) = ∑ i, T (Pi.single i 1) k • zR m i := by sorry
