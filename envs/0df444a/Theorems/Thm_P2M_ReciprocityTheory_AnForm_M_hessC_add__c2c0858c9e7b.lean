-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_add__c2c0858c9e7b
-- name    : P2M_ReciprocityTheory_AnForm_M_hessC_add__c2c0858c9e7b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:31.74534+00:00
-- url     : https://prove2.me/theorems/41224176-03ac-45f4-b8e1-1da7770045b3
-- title:
--   P2 M Reciprocity Theory An Form M hess C add  c2c0858c9e7b: P2 M Reciprocity Theory An Form M hess C add  c2c0858c9e7b
-- statement:
--   The P2 M Reciprocity Theory An Form M hess C add  c2c0858c9e7b construction uses the P2 M Reciprocity Theory An Form M hess C add  c2c0858c9e7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L29-L45

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {D : ℕ}

theorem P2M_ReciprocityTheory_AnForm_M_hessC_add__c2c0858c9e7b (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by sorry

alias «ReciprocityTheory».«AnForm».«M».«hessC_add'» := P2M_ReciprocityTheory_AnForm_M_hessC_add__c2c0858c9e7b
