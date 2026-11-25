-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_mono__c5aa0228de5f
-- name    : P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_mono__c5aa0228de5f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:44:15.344915+00:00
-- url     : https://prove2.me/theorems/6fa06ecb-4ff1-4514-b768-ba7bc05add8b
-- title:
--   P2 M Reciprocity Theory An Form M Fin Hol Atlas Smooth On mono  c5aa0228de5f: P2 M Reciprocity Theory An Form M Fin Hol Atlas Smooth On mono  c5aa0228de5f
-- statement:
--   The P2 M Reciprocity Theory An Form M Fin Hol Atlas Smooth On mono  c5aa0228de5f construction uses the P2 M Reciprocity Theory An Form M Fin Hol Atlas Smooth On mono  c5aa0228de5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L17-L19

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_mono__c5aa0228de5f {A : FinHolAtlas e X} {U V : Set X} {f : X → ℝ}
    (h : A.SmoothOn U f) (hVU : V ⊆ U) : A.SmoothOn V f := by sorry

alias «ReciprocityTheory».«AnForm».«M».«FinHolAtlas».«SmoothOn».«mono'» := P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_mono__c5aa0228de5f
