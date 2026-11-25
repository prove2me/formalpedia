-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_fsPot___coe_5dad99c71fe1
-- name    : P2M_ReciprocityTheory_AnForm_M_fsPot___coe_5dad99c71fe1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:05.578376+00:00
-- url     : https://prove2.me/theorems/62145d6a-388e-46fb-9028-ee07bb9af582
-- title:
--   P2 M Reciprocity Theory An Form M fs Pot   coe 5dad99c71fe1: P2 M Reciprocity Theory An Form M fs Pot   coe 5dad99c71fe1
-- statement:
--   The P2 M Reciprocity Theory An Form M fs Pot   coe 5dad99c71fe1 construction uses the P2 M Reciprocity Theory An Form M fs Pot   coe 5dad99c71fe1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L192-L193

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

theorem P2M_ReciprocityTheory_AnForm_M_fsPot___coe_5dad99c71fe1 (z : ℂ) :
    fsPot.φ (z : OnePoint ℂ) = fun y => (1 / 2) * Real.log (1 + ‖crd0 y‖ ^ 2) := by sorry

alias «ReciprocityTheory».«AnForm».«M».«fsPot_φ_coe» := P2M_ReciprocityTheory_AnForm_M_fsPot___coe_5dad99c71fe1
