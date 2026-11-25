-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_outside
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_outside
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:12.455401+00:00
-- url     : https://prove2.me/theorems/3bb25b67-cf93-5cfe-b38c-90d89ec85831
-- title:
--   Radial Kernel Integrals: lintegral outside
-- statement:
--   The Radial Kernel Integrals construction uses the lintegral outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L59-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L59-L74

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_outside (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ x : ℂ, (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-b))) ‖x‖ =
      ENNReal.ofReal (2 * π * (ρ ^ (2 - b) / (b - 2))) := by sorry
