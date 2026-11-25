-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_mul
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tcoord_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:07.529233+00:00
-- url     : https://prove2.me/theorems/affd864e-8f83-48e3-9dbc-997d4c926610
-- title:
--   Chart: tcoord mul
-- statement:
--   The Chart construction uses the tcoord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/RestrictDiagCompInclFst.lean#L122-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/RestrictDiagCompInclFst.lean#L122-L154

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
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
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

theorem ReciprocityTheory.ChartRestriction.G.Chart.tcoord_mul {w₁ w₂ : sp (R₀ := R) (DualNumber R) ⟶ G} (h₁ : IsTan w₁) (h₂ : IsTan w₂) :
    tcoord hx (w₁ * w₂) (isTan_mul h₁ h₂) = tcoord hx w₁ h₁ + tcoord hx w₂ h₂ := by sorry
