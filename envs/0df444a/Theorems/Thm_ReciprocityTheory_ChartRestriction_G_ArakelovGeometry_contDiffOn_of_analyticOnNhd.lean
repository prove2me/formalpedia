-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_contDiffOn_of_analyticOnNhd
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.contDiffOn_of_analyticOnNhd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:09.790403+00:00
-- url     : https://prove2.me/theorems/d01148c9-ec0d-5561-a207-d1b720f85480
-- title:
--   Arakelov Geometry: cont Diff On of analytic On Nhd
-- statement:
--   The Arakelov Geometry construction uses the cont Diff On of analytic On Nhd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsBoundIteratedFDerivCompact.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsBoundIteratedFDerivCompact.lean#L14-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.contDiffOn_of_analyticOnNhd {D : ℕ} {J : Type} [Fintype J] {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (hγ : AnalyticOnNhd ℂ γ U) : ContDiffOn ℝ ∞ γ U := by sorry
