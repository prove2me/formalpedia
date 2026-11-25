-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_intMat_mulVec_ofReal_754523e05ef9
-- name    : P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_intMat_mulVec_ofReal_754523e05ef9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:51.581338+00:00
-- url     : https://prove2.me/theorems/c50abd41-47c6-4abb-bc6e-2bf079119d02
-- title:
--   P2 M Ground Theory Heights  Heights Regular Kernel Positive int Mat mul Vec of Real 754523e05ef9: P2 M Ground Theory Heights  Heights Regular Kernel Positive int Mat mul Vec of Real 754523e05ef9
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Kernel Positive int Mat mul Vec of Real 754523e05ef9 construction uses the P2 M Ground Theory Heights  Heights Regular Kernel Positive int Mat mul Vec of Real 754523e05ef9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L20-L26

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

theorem P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_intMat_mulVec_ofReal_754523e05ef9 {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℝ)
    (h : B.map (Int.cast : ℤ → ℝ) *ᵥ v = 0) :
    B.map (Int.cast : ℤ → ℂ) *ᵥ (fun k => (v k : ℂ)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«KernelPositive».«intMat_mulVec_ofReal» := P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_intMat_mulVec_ofReal_754523e05ef9
