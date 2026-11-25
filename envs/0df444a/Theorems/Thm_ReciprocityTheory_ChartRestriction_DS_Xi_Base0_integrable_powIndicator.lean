-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_integrable_powIndicator
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.integrable_powIndicator
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:38.546176+00:00
-- url     : https://prove2.me/theorems/902304b7-5e9c-4eeb-bd18-fdaa7cb2b138
-- title:
--   Base0: integrable pow Indicator
-- statement:
--   The Base0 construction uses the integrable pow Indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L21-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L21-L37

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.integrable_powIndicator {β : ℝ} (hβ : β < 1) : Integrable (pw1 β) := by sorry
