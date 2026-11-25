-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adensF_continuousOn
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adensF_continuousOn
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:20:15.770681+00:00
-- url     : https://prove2.me/theorems/d10d2352-ffb9-448e-84de-27f573cdc317
-- title:
--   Arakelov Geometry: adens F continuous On
-- statement:
--   The Arakelov Geometry construction uses the adens F continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L160-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L160-L171

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
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
open scoped ComplexOrder
variable {J : Type} [Fintype J] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adensF_continuousOn {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    {μ : Measure (J → ℂ)} (hsm : IsSmoothMetric m) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) : ContinuousOn (adensF m γ ν) U := by sorry
