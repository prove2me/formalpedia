-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaM_integrableOn_Ioi
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_integrableOn_Ioi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:08:51.567781+00:00
-- url     : https://prove2.me/theorems/0e5a44bb-09f4-5bb2-8e3a-1b5002f93e4c
-- title:
--   Arakelov Geometry: ga M integrable On Ioi
-- statement:
--   The Arakelov Geometry construction uses the ga M integrable On Ioi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMassStA.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMassStA.lean#L45-L50

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_integrableOn_Ioi {b : ℝ} (hb : 0 < b) (j : ℕ) :
    IntegrableOn (fun r : ℝ => r * ((b + r ^ 2) ^ (j + 2))⁻¹) (Ioi 0) := by sorry
