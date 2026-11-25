-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_coeff_X_pow_mul_C
-- name    : ReciprocityTheory.AnForm.P.coeff_X_pow_mul_C
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:33.747644+00:00
-- url     : https://prove2.me/theorems/637a70e4-e140-507f-ab51-0c2a169d04b9
-- title:
--   P: coeff X pow mul C
-- statement:
--   The P construction uses the coeff X pow mul C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L82-L83

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.P.coeff_X_pow_mul_C (a : ℂ) (k n : ℕ) : (X ^ k * C a).coeff n = if n = k then a else 0 := by sorry
