-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_prodPts_tan
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:34.648312+00:00
-- url     : https://prove2.me/theorems/c1a3f80b-55c3-4d3f-b755-88ab257d842e
-- title:
--   Chart: prod Pts tan
-- statement:
--   The Chart construction uses the prod Pts tan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/ChartLaw.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/ChartLaw.lean#L105-L110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

theorem ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan {d : ℕ} (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ G))
    (hv : ∀ i, IsTan (v i)) :
    ∃ h : IsTan (prodPts c v), tcoord hx _ h = ∑ i, c i • tcoord hx (v i) (hv i) := by sorry
