-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_add_log_norm__562736f45a00
-- name    : P2M_ReciprocityTheory_AnForm_A_hessC_add_log_norm__562736f45a00
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:18.362792+00:00
-- url     : https://prove2.me/theorems/0eaa0784-1155-5044-8342-c57973882f04
-- title:
--   P2 M Reciprocity Theory An Form A hess C add log norm  562736f45a00: P2 M Reciprocity Theory An Form A hess C add log norm  562736f45a00
-- statement:
--   The P2 M Reciprocity Theory An Form A hess C add log norm  562736f45a00 construction uses the P2 M Reciprocity Theory An Form A hess C add log norm  562736f45a00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L112-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L112-L119

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

theorem P2M_ReciprocityTheory_AnForm_A_hessC_add_log_norm__562736f45a00 (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by sorry

alias «ReciprocityTheory».«AnForm».«A».«hessC_add_log_norm'» := P2M_ReciprocityTheory_AnForm_A_hessC_add_log_norm__562736f45a00
