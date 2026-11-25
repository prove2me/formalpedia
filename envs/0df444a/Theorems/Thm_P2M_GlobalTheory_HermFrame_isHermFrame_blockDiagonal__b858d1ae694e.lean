-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_isHermFrame_blockDiagonal__b858d1ae694e
-- name    : P2M_GlobalTheory_HermFrame_isHermFrame_blockDiagonal__b858d1ae694e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:57.196302+00:00
-- url     : https://prove2.me/theorems/02e1431e-3b14-4827-8d0b-2afaf9fff8a5
-- title:
--   P2 M Global Theory Herm Frame is Herm Frame block Diagonal  b858d1ae694e: P2 M Global Theory Herm Frame is Herm Frame block Diagonal  b858d1ae694e
-- statement:
--   The P2 M Global Theory Herm Frame is Herm Frame block Diagonal  b858d1ae694e construction uses the P2 M Global Theory Herm Frame is Herm Frame block Diagonal  b858d1ae694e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L153-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L153-L157

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
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem P2M_GlobalTheory_HermFrame_isHermFrame_blockDiagonal__b858d1ae694e {U : Set E} (hU : IsOpen U) (h : ∀ i, IsHermFrame U (H i)) :
    IsHermFrame U fun x => blockDiagonal' fun i => H i x := by sorry

alias «GlobalTheory».«HermFrame».«isHermFrame_blockDiagonal'» := P2M_GlobalTheory_HermFrame_isHermFrame_blockDiagonal__b858d1ae694e
