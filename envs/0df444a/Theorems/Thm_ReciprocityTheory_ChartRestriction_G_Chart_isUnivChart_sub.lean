-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isUnivChart_sub
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.isUnivChart_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:51.966029+00:00
-- url     : https://prove2.me/theorems/1517ef4a-0e29-4ff4-861f-b3daabe1118d
-- title:
--   Chart: is Univ Chart sub
-- statement:
--   The Chart construction uses the is Univ Chart sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L110-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftCompJetSub.lean#L110-L145

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
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Chart.isUnivChart_sub {n d : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (T : (Fin d → R) ≃ₗ[R] (Fin n → R)) :
    IsUnivChart G d (fun m => spMap (jetSub T.toLinearMap m) ≫ x m) := by sorry
