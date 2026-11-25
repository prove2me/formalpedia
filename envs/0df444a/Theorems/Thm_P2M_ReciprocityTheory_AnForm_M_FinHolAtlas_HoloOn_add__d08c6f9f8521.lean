-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_add__d08c6f9f8521
-- name    : P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_add__d08c6f9f8521
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:29.412199+00:00
-- url     : https://prove2.me/theorems/0fe34a24-dd01-5bd9-add7-33cd367b8238
-- title:
--   P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On add  d08c6f9f8521: P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On add  d08c6f9f8521
-- statement:
--   The P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On add  d08c6f9f8521 construction uses the P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On add  d08c6f9f8521 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L21-L23

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

theorem P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_add__d08c6f9f8521 {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x + g x) := by sorry

alias «ReciprocityTheory».«AnForm».«M».«FinHolAtlas».«HoloOn».«add'» := P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_add__d08c6f9f8521
