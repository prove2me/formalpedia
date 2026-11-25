-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_mdisc_comp_perm__2bccc6921bd7
-- name    : P2M_ReciprocityTheory_AnForm_M_mdisc_comp_perm__2bccc6921bd7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:26.106575+00:00
-- url     : https://prove2.me/theorems/da1e43e2-6b98-5446-81d7-c8f4946dbadf
-- title:
--   P2 M Reciprocity Theory An Form M mdisc comp perm  2bccc6921bd7: P2 M Reciprocity Theory An Form M mdisc comp perm  2bccc6921bd7
-- statement:
--   The P2 M Reciprocity Theory An Form M mdisc comp perm  2bccc6921bd7 construction uses the P2 M Reciprocity Theory An Form M mdisc comp perm  2bccc6921bd7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L47-L52

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

theorem P2M_ReciprocityTheory_AnForm_M_mdisc_comp_perm__2bccc6921bd7 (M : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    mdisc (M ∘ σ) = mdisc M := by sorry

alias «ReciprocityTheory».«AnForm».«M».«mdisc_comp_perm'» := P2M_ReciprocityTheory_AnForm_M_mdisc_comp_perm__2bccc6921bd7
