-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexTrans_toAddSubgroup_span_3783b3369c55
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGenIndexTrans_toAddSubgroup_span_3783b3369c55
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:56.759885+00:00
-- url     : https://prove2.me/theorems/20938072-18aa-4dfe-b0f9-d581157c3243
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gen Index Trans to Add Subgroup span 3783b3369c55: P2 M Ground Theory Heights  Heights KLines Gen Index Trans to Add Subgroup span 3783b3369c55
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gen Index Trans to Add Subgroup span 3783b3369c55 construction uses the P2 M Ground Theory Heights  Heights KLines Gen Index Trans to Add Subgroup span 3783b3369c55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexTrans.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexTrans.lean#L9-L11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexTrans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KLinesGenIndexTrans

theorem P2M_GroundTheory_Heights__Heights_KLinesGenIndexTrans_toAddSubgroup_span_3783b3369c55 {V : Type} [AddCommGroup V] (s : Set V) :
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGenIndexTrans».«toAddSubgroup_span» := P2M_GroundTheory_Heights__Heights_KLinesGenIndexTrans_toAddSubgroup_span_3783b3369c55
