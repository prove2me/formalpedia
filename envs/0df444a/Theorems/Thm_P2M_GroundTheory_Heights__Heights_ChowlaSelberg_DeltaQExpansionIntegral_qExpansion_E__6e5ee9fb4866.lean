-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__6e5ee9fb4866
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__6e5ee9fb4866
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:12.132688+00:00
-- url     : https://prove2.me/theorems/a6f1b3e1-e75b-4d39-97e2-8150c440efdf
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion E  6e5ee9fb4866: P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion E  6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion E  6e5ee9fb4866 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion E  6e5ee9fb4866 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/DeltaQExpansionIntegral.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/DeltaQExpansionIntegral.lean#L19-L28

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__6e5ee9fb4866 :
    qExpansion 1 E₄ = map (Int.castRingHom ℂ) (1 + (240 : ℤ) • sigmaSeries 3) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«DeltaQExpansionIntegral».«qExpansion_E₄» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__6e5ee9fb4866
