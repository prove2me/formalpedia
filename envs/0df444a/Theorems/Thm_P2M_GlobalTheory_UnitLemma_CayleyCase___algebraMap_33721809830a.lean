-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_CayleyCase___algebraMap_33721809830a
-- name    : P2M_GlobalTheory_UnitLemma_CayleyCase___algebraMap_33721809830a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:37.616808+00:00
-- url     : https://prove2.me/theorems/e708f633-cb30-45a4-b2d4-fa04a8d72d88
-- title:
--   P2 M Global Theory Unit Lemma Cayley Case   algebra Map 33721809830a: P2 M Global Theory Unit Lemma Cayley Case   algebra Map 33721809830a
-- statement:
--   The P2 M Global Theory Unit Lemma Cayley Case   algebra Map 33721809830a construction uses the P2 M Global Theory Unit Lemma Cayley Case   algebra Map 33721809830a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L166-L168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}

theorem P2M_GlobalTheory_UnitLemma_CayleyCase___algebraMap_33721809830a (B : InvAlg K) (a : K.O) :
    B.σ (algebraMap K.O B.A a) = algebraMap K.E B.A (K.c (algebraMap K.O K.E a)) := by sorry

alias «GlobalTheory».«UnitLemma».«CayleyCase».«σ_algebraMap» := P2M_GlobalTheory_UnitLemma_CayleyCase___algebraMap_33721809830a
