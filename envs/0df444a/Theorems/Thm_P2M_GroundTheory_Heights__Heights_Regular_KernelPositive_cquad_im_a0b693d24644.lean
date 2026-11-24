-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_cquad_im_a0b693d24644
-- name    : P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_cquad_im_a0b693d24644
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:19.730521+00:00
-- url     : https://prove2.me/theorems/8150aa6b-846a-425e-b423-c7de46c99a83
-- title:
--   P2 M Ground Theory Heights  Heights Regular Kernel Positive cquad im a0b693d24644: P2 M Ground Theory Heights  Heights Regular Kernel Positive cquad im a0b693d24644
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Kernel Positive cquad im a0b693d24644 construction uses the P2 M Ground Theory Heights  Heights Regular Kernel Positive cquad im a0b693d24644 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PKernelPositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.KernelPositive

theorem P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_cquad_im_a0b693d24644 {g : ℕ} (v : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ) :
    (cquad v M).im = v ⬝ᵥ (M.map Complex.im *ᵥ v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«KernelPositive».«cquad_im» := P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_cquad_im_a0b693d24644
