-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_plurisubharmonicLocallyIntegrable_holds
-- name    : ReciprocityTheory.AnForm.A.PshMean.plurisubharmonicLocallyIntegrable_holds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:05:17.922981+00:00
-- url     : https://prove2.me/theorems/54e59f5a-bcd9-4833-b087-49c2437b5e28
-- title:
--   Psh Mean: plurisubharmonic Locally Integrable holds
-- statement:
--   The Psh Mean construction uses the plurisubharmonic Locally Integrable holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L158-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L158-L163

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMean
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.PshMean.plurisubharmonicLocallyIntegrable_holds : IsPsh_locallyIntegrableStatement := by sorry
