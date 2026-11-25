-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_Ioc_rpow
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_Ioc_rpow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:06.770355+00:00
-- url     : https://prove2.me/theorems/b9ae1a66-ea67-4351-bb25-d77bf2370571
-- title:
--   Radial Kernel Integrals: lintegral Ioc rpow
-- statement:
--   The Radial Kernel Integrals construction uses the lintegral Ioc rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PlanarKernelBound.lean#L23-L31

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_Ioc_rpow (a ρ : ℝ) (ha : a < 2) (hρ : 0 < ρ) :
    ∫⁻ r in Ioc (0 : ℝ) ρ, ENNReal.ofReal (r ^ (1 - a)) = ENNReal.ofReal (ρ ^ (2 - a) / (2 - a)) := by sorry
