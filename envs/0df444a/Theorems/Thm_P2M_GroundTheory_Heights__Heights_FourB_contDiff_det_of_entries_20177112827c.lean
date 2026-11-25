-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_contDiff_det_of_entries_20177112827c
-- name    : P2M_GroundTheory_Heights__Heights_FourB_contDiff_det_of_entries_20177112827c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:34:35.429454+00:00
-- url     : https://prove2.me/theorems/e04543c7-63f7-43e5-a379-56c5c847b562
-- title:
--   P2 M Ground Theory Heights  Heights Four B cont Diff det of entries 20177112827c: P2 M Ground Theory Heights  Heights Four B cont Diff det of entries 20177112827c
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B cont Diff det of entries 20177112827c construction uses the P2 M Ground Theory Heights  Heights Four B cont Diff det of entries 20177112827c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L26-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Polynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FourB_contDiff_det_of_entries_20177112827c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Type*} [Fintype m] [DecidableEq m] {M : E → Matrix m m ℂ}
    (h : ∀ a b, ContDiff ℝ 2 fun x => M x a b) : ContDiff ℝ 2 fun x => (M x).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«contDiff_det_of_entries» := P2M_GroundTheory_Heights__Heights_FourB_contDiff_det_of_entries_20177112827c
