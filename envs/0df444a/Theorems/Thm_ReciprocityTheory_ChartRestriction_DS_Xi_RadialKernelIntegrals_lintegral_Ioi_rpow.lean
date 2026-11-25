-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_Ioi_rpow
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_Ioi_rpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:39.910862+00:00
-- url     : https://prove2.me/theorems/6c0a5f65-63de-49dc-b5c4-a2132249899a
-- title:
--   Radial Kernel Integrals: lintegral Ioi rpow
-- statement:
--   The Radial Kernel Integrals construction uses the lintegral Ioi rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L33-L40

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_Ioi_rpow (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ r in Ioi ρ, ENNReal.ofReal (r ^ (1 - b)) = ENNReal.ofReal (ρ ^ (2 - b) / (b - 2)) := by sorry
