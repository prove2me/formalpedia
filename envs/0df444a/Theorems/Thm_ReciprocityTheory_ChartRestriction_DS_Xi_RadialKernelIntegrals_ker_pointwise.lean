-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_ker_pointwise
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.ker_pointwise
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:16.245438+00:00
-- url     : https://prove2.me/theorems/0e07425c-1ec9-5cee-b335-405166b7fb83
-- title:
--   Radial Kernel Integrals: ker pointwise
-- statement:
--   The Radial Kernel Integrals construction uses the ker pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L76-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L76-L127

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.ker_pointwise (e γ : ℝ) (he : 0 < e) (heγ : e < γ) (hγ : γ < 2) (c : ℂ) (D ρ : ℝ) (hρ : 0 < ρ)
    (hρc : ‖c‖ ≤ 2 * ρ) (hDρ : D ^ 2 = 4 * ρ ^ 2 - ‖c‖ ^ 2) (x : ℂ) (hx0 : x ≠ 0) (hxc : x ≠ c) :
    ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e / 2)) * ENNReal.ofReal (‖x‖ ^ (-γ)) ≤
      ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
          (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ +
        ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
          (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ +
        ENNReal.ofReal (ρ ^ (-γ)) *
          (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x - c‖ := by sorry
