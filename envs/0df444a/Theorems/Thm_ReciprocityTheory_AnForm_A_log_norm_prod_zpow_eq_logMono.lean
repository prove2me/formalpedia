-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_log_norm_prod_zpow_eq_logMono
-- name    : ReciprocityTheory.AnForm.A.log_norm_prod_zpow_eq_logMono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:31.355339+00:00
-- url     : https://prove2.me/theorems/21daf9cf-d85a-4df2-9a75-46a21244f549
-- title:
--   A: log norm prod zpow eq log Mono
-- statement:
--   The A construction uses the log norm prod zpow eq log Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LogInt.lean#L155-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LogInt.lean#L155-L160

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

theorem ReciprocityTheory.AnForm.A.log_norm_prod_zpow_eq_logMono {D : ℕ} (m : Fin D → ℤ) (z : Fin D → ℂ)
    (hz : ∀ i, z i ≠ 0) : Real.log ‖∏ i, z i ^ m i‖ = logMono m z := by sorry
