-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_Compatible_symm__8f72b4d12959
-- name    : P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_Compatible_symm__8f72b4d12959
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:11:45.912306+00:00
-- url     : https://prove2.me/theorems/bcb0971e-ec70-421f-a47f-a15086beb2e3
-- title:
--   P2 M Reciprocity Theory An Form M Fin Hol Atlas Compatible symm  8f72b4d12959: P2 M Reciprocity Theory An Form M Fin Hol Atlas Compatible symm  8f72b4d12959
-- statement:
--   The P2 M Reciprocity Theory An Form M Fin Hol Atlas Compatible symm  8f72b4d12959 construction uses the P2 M Reciprocity Theory An Form M Fin Hol Atlas Compatible symm  8f72b4d12959 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L42-L43

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_Compatible_symm__8f72b4d12959 {A B : FinHolAtlas e X} (h : A.Compatible B) :
    B.Compatible A := by sorry

alias «ReciprocityTheory».«AnForm».«M».«FinHolAtlas».«Compatible».«symm'» := P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_Compatible_symm__8f72b4d12959
