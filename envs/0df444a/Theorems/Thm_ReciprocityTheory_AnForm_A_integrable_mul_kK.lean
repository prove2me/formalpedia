-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_mul_kK
-- name    : ReciprocityTheory.AnForm.A.integrable_mul_kK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:17.730665+00:00
-- url     : https://prove2.me/theorems/484b06a6-d9f4-4c84-b19e-2cec78a47bfe
-- title:
--   A: integrable mul k K
-- statement:
--   The A construction uses the integrable mul k K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L132-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L132-L136

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.AnForm.A.integrable_mul_kK {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    Integrable (fun h => g h * kK h) := by sorry
