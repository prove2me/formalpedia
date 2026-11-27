-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_mono
-- name    : ReciprocityTheory.AnForm.M.holoOn_mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:39.759229+00:00
-- url     : https://prove2.me/theorems/7009925b-d74a-41d1-a354-f2b3a46d22a6
-- title:
--   M: holo On mono
-- statement:
--   The M construction uses the holo On mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L272-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L272-L275

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.M.holoOn_mono {U V : Set (OnePoint ℂ)} {g : OnePoint ℂ → ℂ} (h : p1.HoloOn U g)
    (hVU : V ⊆ U) : p1.HoloOn V g := by sorry
