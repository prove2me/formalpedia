-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_integrable_reim
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.integrable_reim
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:44.338584+00:00
-- url     : https://prove2.me/theorems/d1361cc7-7fee-45ec-922e-a936874d8d67
-- title:
--   Base0: integrable reim
-- statement:
--   The Base0 construction uses the integrable reim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L39-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.integrable_reim {p q : ℝ → ℝ} (hp : Integrable p) (hq : Integrable q) :
    Integrable (fun z : ℂ => p z.re * q z.im) := by sorry
