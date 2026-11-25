-- Prove2me | Theorems.Thm_P2M_RH_GlobalTheory_UnitLemma_Desc_isIntegral_sigma_9c63cf01f25c1776
-- name    : P2M_RH_GlobalTheory_UnitLemma_Desc_isIntegral_sigma_9c63cf01f25c1776
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:11:28.056137+00:00
-- url     : https://prove2.me/theorems/c04d99c5-8cbc-52eb-b7ac-a2cd867460c1
-- title:
--   P2 M RH Global Theory Unit Lemma Desc is Integral sigma 9c63cf01f25c1776: P2 M RH Global Theory Unit Lemma Desc is Integral sigma 9c63cf01f25c1776
-- statement:
--   The P2 M RH Global Theory Unit Lemma Desc is Integral sigma 9c63cf01f25c1776 construction uses the P2 M RH Global Theory Unit Lemma Desc is Integral sigma 9c63cf01f25c1776 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoPowLowerBoundSwappedPairs.lean#L45-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoPowLowerBoundSwappedPairs.lean#L45-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoPowLowerBoundSwappedPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc

theorem P2M_RH_GlobalTheory_UnitLemma_Desc_isIntegral_sigma_9c63cf01f25c1776 (K : UQ) (B : InvAlg K) (y : B.A) (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by sorry

alias «GlobalTheory».«UnitLemma».«Desc».«isIntegral_sigma» := P2M_RH_GlobalTheory_UnitLemma_Desc_isIntegral_sigma_9c63cf01f25c1776
