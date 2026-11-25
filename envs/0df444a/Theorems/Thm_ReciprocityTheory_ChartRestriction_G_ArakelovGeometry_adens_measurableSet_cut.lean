-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_measurableSet_cut
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_measurableSet_cut
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:50.315643+00:00
-- url     : https://prove2.me/theorems/8d2c1a8c-10ee-4e32-9f3e-85be4aa8a23f
-- title:
--   Arakelov Geometry: adens measurable Set cut
-- statement:
--   The Arakelov Geometry construction uses the adens measurable Set cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStA.lean#L40-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStA.lean#L40-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
variable {J : Type} [Fintype J] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_measurableSet_cut {O : Set (J → ℂ)} {q : (J → ℂ) → Fin D → ℂ} (hO : IsOpen O)
    (hq : ContinuousOn q O) (P : Ideal (MvPolynomial J ℤ)) {A : Set (Fin D → ℂ)}
    (hA : MeasurableSet A) : MeasurableSet {z | z ∈ O ∧ z ∈ pts P ∧ q z ∈ A} := by sorry
