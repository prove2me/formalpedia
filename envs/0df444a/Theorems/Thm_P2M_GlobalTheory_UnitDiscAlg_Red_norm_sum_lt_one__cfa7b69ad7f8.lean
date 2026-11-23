-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitDiscAlg_Red_norm_sum_lt_one__cfa7b69ad7f8
-- name    : P2M_GlobalTheory_UnitDiscAlg_Red_norm_sum_lt_one__cfa7b69ad7f8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:39.007926+00:00
-- url     : https://prove2.me/theorems/d8ffbfec-b6bb-4b3a-a079-06b049ff093c
-- title:
--   P2 M Global Theory Unit Disc Alg Red norm sum lt one  cfa7b69ad7f8: P2 M Global Theory Unit Disc Alg Red norm sum lt one  cfa7b69ad7f8
-- statement:
--   The P2 M Global Theory Unit Disc Alg Red norm sum lt one  cfa7b69ad7f8 construction uses the P2 M Global Theory Unit Disc Alg Red norm sum lt one  cfa7b69ad7f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L22-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem P2M_GlobalTheory_UnitDiscAlg_Red_norm_sum_lt_one__cfa7b69ad7f8 {s : Finset (Fin n)} {f : Fin n → E} (h : ∀ k, ‖f k‖ < 1) :
    ‖∑ k ∈ s, f k‖ < 1 := by sorry

alias «GlobalTheory».«UnitDiscAlg».«Red».«norm_sum_lt_one'» := P2M_GlobalTheory_UnitDiscAlg_Red_norm_sum_lt_one__cfa7b69ad7f8
