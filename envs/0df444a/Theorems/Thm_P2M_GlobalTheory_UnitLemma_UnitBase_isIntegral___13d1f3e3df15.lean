-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase_isIntegral___13d1f3e3df15
-- name    : P2M_GlobalTheory_UnitLemma_UnitBase_isIntegral___13d1f3e3df15
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:09.855567+00:00
-- url     : https://prove2.me/theorems/625eea42-bbd6-4d3d-ad03-043e6aca5bd1
-- title:
--   P2 M Global Theory Unit Lemma Unit Base is Integral   13d1f3e3df15: P2 M Global Theory Unit Lemma Unit Base is Integral   13d1f3e3df15
-- statement:
--   The P2 M Global Theory Unit Lemma Unit Base is Integral   13d1f3e3df15 construction uses the P2 M Global Theory Unit Lemma Unit Base is Integral   13d1f3e3df15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L139-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L139-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial

theorem P2M_GlobalTheory_UnitLemma_UnitBase_isIntegral___13d1f3e3df15 {K : UQ} (B : InvAlg K) {y : B.A} (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by sorry

alias «GlobalTheory».«UnitLemma».«UnitBase».«isIntegral_σ» := P2M_GlobalTheory_UnitLemma_UnitBase_isIntegral___13d1f3e3df15
