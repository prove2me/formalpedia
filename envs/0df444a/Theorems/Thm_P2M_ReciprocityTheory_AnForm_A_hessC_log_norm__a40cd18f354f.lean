-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_log_norm__a40cd18f354f
-- name    : P2M_ReciprocityTheory_AnForm_A_hessC_log_norm__a40cd18f354f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:29.665025+00:00
-- url     : https://prove2.me/theorems/76c70a77-b387-4192-98a7-e62165f42b55
-- title:
--   P2 M Reciprocity Theory An Form A hess C log norm  a40cd18f354f: P2 M Reciprocity Theory An Form A hess C log norm  a40cd18f354f
-- statement:
--   The P2 M Reciprocity Theory An Form A hess C log norm  a40cd18f354f construction uses the P2 M Reciprocity Theory An Form A hess C log norm  a40cd18f354f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L106-L110

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

theorem P2M_ReciprocityTheory_AnForm_A_hessC_log_norm__a40cd18f354f (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by sorry

alias «ReciprocityTheory».«AnForm».«A».«hessC_log_norm'» := P2M_ReciprocityTheory_AnForm_A_hessC_log_norm__a40cd18f354f
