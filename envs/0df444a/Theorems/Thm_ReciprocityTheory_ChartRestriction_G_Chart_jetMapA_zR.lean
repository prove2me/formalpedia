-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetMapA_zR
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jetMapA_zR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:22.720892+00:00
-- url     : https://prove2.me/theorems/0f74901d-80fd-45ca-826d-81ba75b03d9e
-- title:
--   Chart: jet Map A z R
-- statement:
--   The Chart construction uses the jet Map A z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsUnivRingBc.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsUnivRingBc.lean#L29-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
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
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] (eps : B →ₐ[R] R) {n : ℕ}
variable {R' : Type} [CommRing R'] [Algebra R R']

theorem ReciprocityTheory.ChartRestriction.G.Chart.jetMapA_zR (m : ℕ) (j : Fin n) : jetMapA (R := R) (R' := R') n m (zR m j) = zR m j := by sorry
