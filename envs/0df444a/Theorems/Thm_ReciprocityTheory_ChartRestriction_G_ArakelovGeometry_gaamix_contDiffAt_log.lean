-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaamix_contDiffAt_log
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_contDiffAt_log
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:26.434567+00:00
-- url     : https://prove2.me/theorems/b0af38a3-47b1-4391-90f0-9823ec5695da
-- title:
--   Arakelov Geometry: gaamix cont Diff At log
-- statement:
--   The Arakelov Geometry construction uses the gaamix cont Diff At log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMixSt.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMixSt.lean#L47-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology ContDiff
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_contDiffAt_log {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m)
    {γ : (Fin D → ℂ) → Ix κ → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : γ y ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (m.ρ (γ y'))) y := by sorry
