-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_aug_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.aug_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:40.770207+00:00
-- url     : https://prove2.me/theorems/e5751198-c808-4ee7-9f36-93d41358eca8
-- title:
--   Chart: aug iff
-- statement:
--   The Chart construction uses the aug iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/ChartLawPf.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/ChartLawPf.lean#L29-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
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

theorem ReciprocityTheory.ChartRestriction.G.Chart.aug_iff {κ : Type} {d m : ℕ} (ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m) :
    (jetAug R κ m).comp ψ = jetAug R (Fin d) m ↔ ∀ j, jetZeroR R κ m (ψ (zR m j)) = 0 := by sorry
