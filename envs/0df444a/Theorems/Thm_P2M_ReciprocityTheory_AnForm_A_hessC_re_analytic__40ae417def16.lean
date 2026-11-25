-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_re_analytic__40ae417def16
-- name    : P2M_ReciprocityTheory_AnForm_A_hessC_re_analytic__40ae417def16
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:17.006257+00:00
-- url     : https://prove2.me/theorems/d45e2990-0ddd-4953-918a-837fbac50319
-- title:
--   P2 M Reciprocity Theory An Form A hess C re analytic  40ae417def16: P2 M Reciprocity Theory An Form A hess C re analytic  40ae417def16
-- statement:
--   The P2 M Reciprocity Theory An Form A hess C re analytic  40ae417def16 construction uses the P2 M Reciprocity Theory An Form A hess C re analytic  40ae417def16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L81-L82

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

theorem P2M_ReciprocityTheory_AnForm_A_hessC_re_analytic__40ae417def16 (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => (G w).re) z = 0 := by sorry

alias «ReciprocityTheory».«AnForm».«A».«hessC_re_analytic'» := P2M_ReciprocityTheory_AnForm_A_hessC_re_analytic__40ae417def16
