-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_PolynomialGrowthIntegrals_slowWeight_le
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.slowWeight_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:39.898307+00:00
-- url     : https://prove2.me/theorems/ef798670-377b-5287-a2f6-71928466ccaa
-- title:
--   Polynomial Growth Integrals: slow Weight le
-- statement:
--   The Polynomial Growth Integrals construction uses the slow Weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SlowWeightBound.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SlowWeightBound.lean#L69-L77

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.slowWeight_le {n : ℕ} {t A b : Fin n → ℝ} {R β β' : ℝ} (hR : 0 < R) (ht : ∀ i, 0 ≤ t i)
    (hA : ∀ i, R ≤ A i) (hβ : |β| ≤ R) (hβ' : |β'| ≤ R) :
    slowly t A b β ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * slowly t A b β' := by sorry
