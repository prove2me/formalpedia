-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_add__d2d06fbdee79
-- name    : P2M_ReciprocityTheory_AnForm_A_hessC_add__d2d06fbdee79
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:41.853257+00:00
-- url     : https://prove2.me/theorems/d7497296-1351-4f55-8488-6f5c5ea6b46b
-- title:
--   P2 M Reciprocity Theory An Form A hess C add  d2d06fbdee79: P2 M Reciprocity Theory An Form A hess C add  d2d06fbdee79
-- statement:
--   The P2 M Reciprocity Theory An Form A hess C add  d2d06fbdee79 construction uses the P2 M Reciprocity Theory An Form A hess C add  d2d06fbdee79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L28-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/CovLog.lean#L28-L48

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

theorem P2M_ReciprocityTheory_AnForm_A_hessC_add__d2d06fbdee79 (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by sorry

alias «ReciprocityTheory».«AnForm».«A».«hessC_add'» := P2M_ReciprocityTheory_AnForm_A_hessC_add__d2d06fbdee79
