-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_im_pos_of_punctured_925a660c5ab1
-- name    : P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_im_pos_of_punctured_925a660c5ab1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:31.522802+00:00
-- url     : https://prove2.me/theorems/f65b4d3c-ff63-5cc8-a360-5e2544ac0024
-- title:
--   P2 M Ground Theory Heights  Heights Regular Kernel Positive im pos of punctured 925a660c5ab1: P2 M Ground Theory Heights  Heights Regular Kernel Positive im pos of punctured 925a660c5ab1
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Kernel Positive im pos of punctured 925a660c5ab1 construction uses the P2 M Ground Theory Heights  Heights Regular Kernel Positive im pos of punctured 925a660c5ab1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L28-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L28-L55

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

theorem P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_im_pos_of_punctured_925a660c5ab1 {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hpos : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 < (h t).im) : 0 < (h 0).im := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«KernelPositive».«im_pos_of_punctured» := P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_im_pos_of_punctured_925a660c5ab1
