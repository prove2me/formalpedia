-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_norm_det_sq_le_fb621fa6f07e
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_norm_det_sq_le_fb621fa6f07e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:44.326422+00:00
-- url     : https://prove2.me/theorems/d3d68fd2-98a7-4dff-bfe0-13cc3472c043
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail norm det sq le fb621fa6f07e: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail norm det sq le fb621fa6f07e
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail norm det sq le fb621fa6f07e construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail norm det sq le fb621fa6f07e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L157-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L157-L172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_norm_det_sq_le_fb621fa6f07e {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) :
    ‖(coordPlaneBlock π).det‖ ^ 2 ≤ (Fintype.card (Equiv.Perm (Fin m)) : ℝ) *
      ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«norm_det_sq_le» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_norm_det_sq_le_fb621fa6f07e
