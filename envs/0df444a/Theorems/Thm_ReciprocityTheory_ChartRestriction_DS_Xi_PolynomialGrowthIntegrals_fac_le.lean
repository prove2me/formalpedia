-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_PolynomialGrowthIntegrals_fac_le
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.fac_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:10.070465+00:00
-- url     : https://prove2.me/theorems/c0f061e2-37e8-5326-8a34-7c591cfd7bee
-- title:
--   Polynomial Growth Integrals: fac le
-- statement:
--   The Polynomial Growth Integrals construction uses the fac le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SlowWeightBound.lean#L49-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SlowWeightBound.lean#L49-L67

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.fac_le {A b t β β' R : ℝ} (hR : 0 < R) (hA : R ≤ A) (ht : 0 ≤ t) (hβ : |β| ≤ R)
    (hβ' : |β'| ≤ R) :
    (A ^ 2 + (β - b) ^ 2) ^ (-t / 2) ≤ 3 ^ t * (A ^ 2 + (β' - b) ^ 2) ^ (-t / 2) := by sorry
