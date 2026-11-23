-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_radial
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_radial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:08.950249+00:00
-- url     : https://prove2.me/theorems/54e500c8-641b-4694-83d9-934db6ba701f
-- title:
--   Radial Kernel Integrals: lintegral radial
-- statement:
--   The Radial Kernel Integrals construction uses the lintegral radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L8-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PlanarKernelBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_radial (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, g ‖x‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by sorry
