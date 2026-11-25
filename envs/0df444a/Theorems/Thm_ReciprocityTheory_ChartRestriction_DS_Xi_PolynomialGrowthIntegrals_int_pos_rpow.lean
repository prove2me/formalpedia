-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_PolynomialGrowthIntegrals_int_pos_rpow
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.int_pos_rpow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:32.539017+00:00
-- url     : https://prove2.me/theorems/90422a9c-a060-5db1-b02f-d322f4f3ac1d
-- title:
--   Polynomial Growth Integrals: int pos rpow
-- statement:
--   The Polynomial Growth Integrals construction uses the int pos rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SlowWeightBound.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SlowWeightBound.lean#L11-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SlowWeightBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals

theorem ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.int_pos_rpow {R κ : ℝ} (hR : 0 < R) (hκ : κ < 1) :
    ∫⁻ β in Ioc 0 R, ENNReal.ofReal (β ^ (-κ)) = ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by sorry
