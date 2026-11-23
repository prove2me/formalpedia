-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_exists_re_analytic_eq_log_norm
-- name    : ReciprocityTheory.AnForm.A.exists_re_analytic_eq_log_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:38.347896+00:00
-- url     : https://prove2.me/theorems/aea9d121-c575-404a-aa23-9329c8826573
-- title:
--   A: exists re analytic eq log norm
-- statement:
--   The A construction uses the exists re analytic eq log norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L91-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L91-L104

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Complex Filter Topology
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.exists_re_analytic_eq_log_norm (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticAt ℂ G z ∧
      (fun w => Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => (G w).re := by sorry
