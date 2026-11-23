-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_eps
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.pt_eps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:41.348338+00:00
-- url     : https://prove2.me/theorems/33e3c3e7-651d-4cd4-8c69-89813b95d637
-- title:
--   Chart: pt eps
-- statement:
--   The Chart construction uses the pt eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L176-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L176-L186

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
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
variable {R₀ : Type} [CommRing R₀]
variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Chart.pt_eps (C : Chart G) (P : Type) [CommRing P] [Algebra R₀ P] :
    pt C ((Algebra.ofId R₀ P).comp (eps C)) = (1 : sp P ⟶ G) := by sorry
