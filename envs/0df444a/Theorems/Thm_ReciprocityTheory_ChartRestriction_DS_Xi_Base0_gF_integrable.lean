-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_gF_integrable
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.gF_integrable
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:46:27.995451+00:00
-- url     : https://prove2.me/theorems/394ef9ee-5eec-4197-8777-edc1e8c8f256
-- title:
--   Base0: g F integrable
-- statement:
--   The Base0 construction uses the g F integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L165-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L165-L185

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.gF_integrable (p q : ι) {β : ℝ} (hβ : β < 1) (i : ι) : Integrable (gF p q β i) := by sorry
