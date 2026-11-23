-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_isLieBasis
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:33.553791+00:00
-- url     : https://prove2.me/theorems/da9fefe3-1c03-44cd-9945-05fa59d03262
-- title:
--   Chart: exists is Lie Basis
-- statement:
--   The Chart construction uses the exists is Lie Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/ChartLawPf.lean#L91-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/ChartLawPf.lean#L91-L113

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
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (hsm : Smooth G.hom) :
    ∃ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v := by sorry
