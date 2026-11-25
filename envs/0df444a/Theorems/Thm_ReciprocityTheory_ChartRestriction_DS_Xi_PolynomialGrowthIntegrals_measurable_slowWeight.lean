-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_PolynomialGrowthIntegrals_measurable_slowWeight
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.measurable_slowWeight
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:06.10779+00:00
-- url     : https://prove2.me/theorems/dc9a4210-0406-4bb3-884c-5531ae8ce035
-- title:
--   Polynomial Growth Integrals: measurable slow Weight
-- statement:
--   The Polynomial Growth Integrals construction uses the measurable slow Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SlowWeightBound.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SlowWeightBound.lean#L79-L81

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.measurable_slowWeight {n : ℕ} (t A b : Fin n → ℝ) : Measurable (slowly t A b) := by sorry
