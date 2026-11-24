-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_fderiv_fderiv_gbPot_apply
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.fderiv_fderiv_gbPot_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:30.24542+00:00
-- url     : https://prove2.me/theorems/004b7545-fdd1-46f7-84d3-1cf7356aa5d3
-- title:
--   Arakelov Geometry: fderiv fderiv gb Pot apply
-- statement:
--   The Arakelov Geometry construction uses the fderiv fderiv gb Pot apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMassStA.lean#L230-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMassStA.lean#L230-L235

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
open ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.fderiv_fderiv_gbPot_apply (y v u : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ gbPot) y v u =
      (gbG y)⁻¹ * gbBil D v u - 2 * ((gbG y) ^ 2)⁻¹ * gbBil D y v * gbBil D y u := by sorry
