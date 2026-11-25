-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_isHermitian__4fd7a1bbb7ba
-- name    : P2M_ReciprocityTheory_AnForm_M_hessC_isHermitian__4fd7a1bbb7ba
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:42.143948+00:00
-- url     : https://prove2.me/theorems/b8709603-2c73-5a33-ad4d-38d7f9d7b52a
-- title:
--   P2 M Reciprocity Theory An Form M hess C is Hermitian  4fd7a1bbb7ba: P2 M Reciprocity Theory An Form M hess C is Hermitian  4fd7a1bbb7ba
-- statement:
--   The P2 M Reciprocity Theory An Form M hess C is Hermitian  4fd7a1bbb7ba construction uses the P2 M Reciprocity Theory An Form M hess C is Hermitian  4fd7a1bbb7ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L71-L78

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

theorem P2M_ReciprocityTheory_AnForm_M_hessC_isHermitian__4fd7a1bbb7ba (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by sorry

alias «ReciprocityTheory».«AnForm».«M».«hessC_isHermitian'» := P2M_ReciprocityTheory_AnForm_M_hessC_isHermitian__4fd7a1bbb7ba
