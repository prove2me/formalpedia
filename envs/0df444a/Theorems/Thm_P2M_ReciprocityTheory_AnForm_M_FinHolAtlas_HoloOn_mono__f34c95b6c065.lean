-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mono__f34c95b6c065
-- name    : P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mono__f34c95b6c065
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:23.194252+00:00
-- url     : https://prove2.me/theorems/6841e025-1129-5ca8-ab5e-6ca9e7ff6e3c
-- title:
--   P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On mono  f34c95b6c065: P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On mono  f34c95b6c065
-- statement:
--   The P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On mono  f34c95b6c065 construction uses the P2 M Reciprocity Theory An Form M Fin Hol Atlas Holo On mono  f34c95b6c065 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L13-L15

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

theorem P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mono__f34c95b6c065 {A : FinHolAtlas e X} {U V : Set X} {g : X → ℂ}
    (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g := by sorry

alias «ReciprocityTheory».«AnForm».«M».«FinHolAtlas».«HoloOn».«mono'» := P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mono__f34c95b6c065
