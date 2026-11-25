-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_add__cc2e4aa96313
-- name    : P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_add__cc2e4aa96313
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:44:34.209312+00:00
-- url     : https://prove2.me/theorems/78d496b5-c451-448f-b2e3-f26ed19bdf94
-- title:
--   P2 M Reciprocity Theory An Form M Fin Hol Atlas Smooth On add  cc2e4aa96313: P2 M Reciprocity Theory An Form M Fin Hol Atlas Smooth On add  cc2e4aa96313
-- statement:
--   The P2 M Reciprocity Theory An Form M Fin Hol Atlas Smooth On add  cc2e4aa96313 construction uses the P2 M Reciprocity Theory An Form M Fin Hol Atlas Smooth On add  cc2e4aa96313 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L33-L35

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

theorem P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_add__cc2e4aa96313 {A : FinHolAtlas e X} {U : Set X} {f g : X → ℝ}
    (hf : A.SmoothOn U f) (hg : A.SmoothOn U g) : A.SmoothOn U (fun x => f x + g x) := by sorry

alias «ReciprocityTheory».«AnForm».«M».«FinHolAtlas».«SmoothOn».«add'» := P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_add__cc2e4aa96313
