-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaM_lintegral_pi
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_lintegral_pi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:42.01863+00:00
-- url     : https://prove2.me/theorems/cd63d636-b7c8-485f-b312-a7d75e5c632f
-- title:
--   Arakelov Geometry: ga M lintegral pi
-- statement:
--   The Arakelov Geometry construction uses the ga M lintegral pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMassStA.lean#L87-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMassStA.lean#L87-L142

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
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
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_lintegral_pi (D : ℕ) : ∀ (a : ℝ), 0 < a → ∀ j : ℕ,
    ∫⁻ y : Fin D → ℂ, ENNReal.ofReal (((a + ∑ i, ‖y i‖ ^ 2) ^ (D + j + 1))⁻¹) =
      ENNReal.ofReal (Real.pi ^ D * (j.factorial : ℝ) / (((D + j).factorial : ℝ) * a ^ (j + 1))) := by sorry
