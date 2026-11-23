-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase___algebraMap_O_5df93c796371
-- name    : P2M_GlobalTheory_UnitLemma_UnitBase___algebraMap_O_5df93c796371
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:23.18605+00:00
-- url     : https://prove2.me/theorems/d50dd060-017d-4f5a-b20d-3211ab1a35f7
-- title:
--   P2 M Global Theory Unit Lemma Unit Base   algebra Map O 5df93c796371: P2 M Global Theory Unit Lemma Unit Base   algebra Map O 5df93c796371
-- statement:
--   The P2 M Global Theory Unit Lemma Unit Base   algebra Map O 5df93c796371 construction uses the P2 M Global Theory Unit Lemma Unit Base   algebra Map O 5df93c796371 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L134-L137

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

theorem P2M_GlobalTheory_UnitLemma_UnitBase___algebraMap_O_5df93c796371 {K : UQ} (B : InvAlg K) (x : K.O) :
    B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A (cO K x) := by sorry

alias «GlobalTheory».«UnitLemma».«UnitBase».«σ_algebraMap_O» := P2M_GlobalTheory_UnitLemma_UnitBase___algebraMap_O_5df93c796371
