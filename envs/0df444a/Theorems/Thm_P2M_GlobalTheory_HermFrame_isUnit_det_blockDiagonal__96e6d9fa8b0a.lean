-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_isUnit_det_blockDiagonal__96e6d9fa8b0a
-- name    : P2M_GlobalTheory_HermFrame_isUnit_det_blockDiagonal__96e6d9fa8b0a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:01.92988+00:00
-- url     : https://prove2.me/theorems/da4f5b3e-eb8b-4971-b071-b1c4b14cb97b
-- title:
--   P2 M Global Theory Herm Frame is Unit det block Diagonal  96e6d9fa8b0a: P2 M Global Theory Herm Frame is Unit det block Diagonal  96e6d9fa8b0a
-- statement:
--   The P2 M Global Theory Herm Frame is Unit det block Diagonal  96e6d9fa8b0a construction uses the P2 M Global Theory Herm Frame is Unit det block Diagonal  96e6d9fa8b0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L123-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {o : Type*} [DecidableEq o] {m m' : o → Type*}
variable [Fintype o] [∀ i, Fintype (m i)] [∀ i, Fintype (m' i)]
variable [∀ i, DecidableEq (m i)] {H : ∀ i, E → Matrix (m i) (m i) ℂ} {z : E}

theorem P2M_GlobalTheory_HermFrame_isUnit_det_blockDiagonal__96e6d9fa8b0a {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, IsUnit (A i).det) :
    IsUnit (blockDiagonal' A).det := by sorry

alias «GlobalTheory».«HermFrame».«isUnit_det_blockDiagonal'» := P2M_GlobalTheory_HermFrame_isUnit_det_blockDiagonal__96e6d9fa8b0a
