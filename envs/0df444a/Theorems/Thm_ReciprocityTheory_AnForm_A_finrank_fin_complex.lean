-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_finrank_fin_complex
-- name    : ReciprocityTheory.AnForm.A.finrank_fin_complex
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:01.275795+00:00
-- url     : https://prove2.me/theorems/feec7da9-f8de-4889-94b5-1d4a4046e47c
-- title:
--   A: finrank fin complex
-- statement:
--   The A construction uses the finrank fin complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L12-L13

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.finrank_fin_complex : Module.finrank ℝ (Fin D → ℂ) = 2 * D := by sorry
