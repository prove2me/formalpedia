-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mul__28453790b1f6
-- name    : P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mul__28453790b1f6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:53.956632+00:00
-- url     : https://prove2.me/theorems/6f3d8ea8-88a3-4074-b55e-ef350c2ced57
-- title:
--   P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On mul  28453790b1f6: P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On mul  28453790b1f6
-- statement:
--   The P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On mul  28453790b1f6 construction uses the P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On mul  28453790b1f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L29-L31

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

theorem P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mul__28453790b1f6 {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x * g x) := by sorry

alias «ReciprocityTheory».«AnForm».«M».«FinHolAtlas».«HoloOn».«mul'» := P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mul__28453790b1f6
