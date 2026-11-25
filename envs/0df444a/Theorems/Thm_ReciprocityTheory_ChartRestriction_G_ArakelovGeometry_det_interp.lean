-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_det_interp
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.det_interp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:25.685858+00:00
-- url     : https://prove2.me/theorems/0e779293-0c02-5c9c-b7e7-3e4d6d8e6ca3
-- title:
--   Arakelov Geometry: det interp
-- statement:
--   The Arakelov Geometry construction uses the det interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMixSt.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMixSt.lean#L12-L17

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.det_interp (M₀ M₁ : Matrix (Fin D) (Fin D) ℂ) (t : ℂ) :
    ((1 - t) • M₀ + t • M₁).det = ∑ i ∈ Finset.range (D + 1),
      (D.choose i : ℂ) * t ^ i * (1 - t) ^ (D - i) *
        mixedDisc (fun j : Fin D => if j.val < i then M₁ else M₀) := by sorry
