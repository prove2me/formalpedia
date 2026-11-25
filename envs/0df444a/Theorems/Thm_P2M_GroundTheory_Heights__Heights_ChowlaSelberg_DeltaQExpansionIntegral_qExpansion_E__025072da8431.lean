-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__025072da8431
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__025072da8431
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:03.981083+00:00
-- url     : https://prove2.me/theorems/db9bb671-c13c-4820-ac16-d24f170175c6
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion E  025072da8431: P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion E  02
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion E  025072da8431 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Delta QExpansion Integral q Expansion E  025072da8431 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/DeltaQExpansionIntegral.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/DeltaQExpansionIntegral.lean#L30-L39

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__025072da8431 :
    qExpansion 1 E₆ = map (Int.castRingHom ℂ) (1 - (504 : ℤ) • sigmaSeries 5) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«DeltaQExpansionIntegral».«qExpansion_E₆» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__025072da8431
