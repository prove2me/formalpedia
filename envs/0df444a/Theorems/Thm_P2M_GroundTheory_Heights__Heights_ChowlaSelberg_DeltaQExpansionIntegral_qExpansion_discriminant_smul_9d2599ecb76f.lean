-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_discriminant_smul_9d2599ecb76f
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_discriminant_smul_9d2599ecb76f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:00.612227+00:00
-- url     : https://prove2.me/theorems/64708370-5630-563f-9138-a35a2d048487
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion discriminant smul 9d2599ecb76f: P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion discriminant smul 9d2599ecb76f construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion discriminant smul 9d2599ecb76f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/DeltaQExpansionIntegral.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/DeltaQExpansionIntegral.lean#L60-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaQExpansionIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open UpperHalfPlane ModularForm EisensteinSeries PowerSeries ArithmeticFunction
open scoped MatrixGroups ArithmeticFunction.sigma
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.DeltaQExpansionIntegral

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_discriminant_smul_9d2599ecb76f :
    (1728 : ℂ) • qExpansion 1 ModularForm.discriminant =
      qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«DeltaQExpansionIntegral».«qExpansion_discriminant_smul» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_discriminant_smul_9d2599ecb76f
