-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_add_re_analytic__51ad31de6cad
-- name    : P2M_ReciprocityTheory_AnForm_A_hessC_add_re_analytic__51ad31de6cad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:17.806294+00:00
-- url     : https://prove2.me/theorems/1ee2f1b3-be76-497b-8029-9aa8105c0977
-- title:
--   P2 M Reciprocity Theory An Form A hess C add re analytic  51ad31de6cad: P2 M Reciprocity Theory An Form A hess C add re analytic  51ad31de6cad
-- statement:
--   The P2 M Reciprocity Theory An Form A hess C add re analytic  51ad31de6cad construction uses the P2 M Reciprocity Theory An Form A hess C add re analytic  51ad31de6cad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L84-L89

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

theorem P2M_ReciprocityTheory_AnForm_A_hessC_add_re_analytic__51ad31de6cad (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by sorry

alias «ReciprocityTheory».«AnForm».«A».«hessC_add_re_analytic'» := P2M_ReciprocityTheory_AnForm_A_hessC_add_re_analytic__51ad31de6cad
