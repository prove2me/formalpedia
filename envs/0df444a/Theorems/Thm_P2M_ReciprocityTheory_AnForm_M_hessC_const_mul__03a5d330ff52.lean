-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_const_mul__03a5d330ff52
-- name    : P2M_ReciprocityTheory_AnForm_M_hessC_const_mul__03a5d330ff52
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:47.2709+00:00
-- url     : https://prove2.me/theorems/457ba12b-47bc-4e1d-86c2-d35268566880
-- title:
--   P2 M Reciprocity Theory An Form M hess C const mul  03a5d330ff52: P2 M Reciprocity Theory An Form M hess C const mul  03a5d330ff52
-- statement:
--   The P2 M Reciprocity Theory An Form M hess C const mul  03a5d330ff52 construction uses the P2 M Reciprocity Theory An Form M hess C const mul  03a5d330ff52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L16-L27

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

theorem P2M_ReciprocityTheory_AnForm_M_hessC_const_mul__03a5d330ff52 (c : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    hessC (fun w => c * φ w) z = (c : ℂ) • hessC φ z := by sorry

alias «ReciprocityTheory».«AnForm».«M».«hessC_const_mul'» := P2M_ReciprocityTheory_AnForm_M_hessC_const_mul__03a5d330ff52
