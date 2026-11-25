-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_ca_const_mul
-- name    : ReciprocityTheory.AnForm.A.ca_const_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:14.459+00:00
-- url     : https://prove2.me/theorems/4f67a4d7-009e-4a4b-ae1b-f5a271d2ca63
-- title:
--   A: ca const mul
-- statement:
--   The A construction uses the ca const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L107-L110

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
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
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.ca_const_mul (c : ℝ) (f : ℂ → ℝ) :
    Real.circleAverage (fun ζ => c * f ζ) 0 1 = c * Real.circleAverage f 0 1 := by sorry
