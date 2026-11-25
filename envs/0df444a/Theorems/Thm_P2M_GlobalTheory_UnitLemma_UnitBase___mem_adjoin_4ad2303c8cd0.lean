-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase___mem_adjoin_4ad2303c8cd0
-- name    : P2M_GlobalTheory_UnitLemma_UnitBase___mem_adjoin_4ad2303c8cd0
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:53.658471+00:00
-- url     : https://prove2.me/theorems/bd4e3a59-47b6-4e5c-81e2-d9594af236f3
-- title:
--   P2 M Global Theory Unit Lemma Unit Base   mem adjoin 4ad2303c8cd0: P2 M Global Theory Unit Lemma Unit Base   mem adjoin 4ad2303c8cd0
-- statement:
--   The P2 M Global Theory Unit Lemma Unit Base   mem adjoin 4ad2303c8cd0 construction uses the P2 M Global Theory Unit Lemma Unit Base   mem adjoin 4ad2303c8cd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L148-L156

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

theorem P2M_GlobalTheory_UnitLemma_UnitBase___mem_adjoin_4ad2303c8cd0 {K : UQ} (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (hint : IsIntegral K.O B.g)
    {y : B.A} (hy : y ∈ Algebra.adjoin K.O {B.g}) : B.σ y ∈ Algebra.adjoin K.O {B.g} := by sorry

alias «GlobalTheory».«UnitLemma».«UnitBase».«σ_mem_adjoin» := P2M_GlobalTheory_UnitLemma_UnitBase___mem_adjoin_4ad2303c8cd0
