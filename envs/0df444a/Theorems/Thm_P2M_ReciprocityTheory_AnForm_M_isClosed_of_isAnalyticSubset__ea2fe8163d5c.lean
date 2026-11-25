-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_isClosed_of_isAnalyticSubset__ea2fe8163d5c
-- name    : P2M_ReciprocityTheory_AnForm_M_isClosed_of_isAnalyticSubset__ea2fe8163d5c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:58.093118+00:00
-- url     : https://prove2.me/theorems/bb07622c-be08-5077-967f-ad29cf0f30cd
-- title:
--   P2 M Reciprocity Theory An Form M is Closed of is Analytic Subset  ea2fe8163d5c: P2 M Reciprocity Theory An Form M is Closed of is Analytic Subset  ea2fe8163d5c
-- statement:
--   The P2 M Reciprocity Theory An Form M is Closed of is Analytic Subset  ea2fe8163d5c construction uses the P2 M Reciprocity Theory An Form M is Closed of is Analytic Subset  ea2fe8163d5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeSheets.lean#L16-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeSheets.lean#L16-L48

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeSheets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open FinHolAtlas Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem P2M_ReciprocityTheory_AnForm_M_isClosed_of_isAnalyticSubset__ea2fe8163d5c (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by sorry

alias «ReciprocityTheory».«AnForm».«M».«isClosed_of_isAnalyticSubset'» := P2M_ReciprocityTheory_AnForm_M_isClosed_of_isAnalyticSubset__ea2fe8163d5c
