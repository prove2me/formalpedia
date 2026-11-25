-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_posDef_blockDiagonal__3fab605ad041
-- name    : P2M_GlobalTheory_HermFrame_posDef_blockDiagonal__3fab605ad041
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:48.476813+00:00
-- url     : https://prove2.me/theorems/901def52-afc4-44a3-b0ed-fdb140ab103a
-- title:
--   P2 M Global Theory Herm Frame pos Def block Diagonal  3fab605ad041: P2 M Global Theory Herm Frame pos Def block Diagonal  3fab605ad041
-- statement:
--   The P2 M Global Theory Herm Frame pos Def block Diagonal  3fab605ad041 construction uses the P2 M Global Theory Herm Frame pos Def block Diagonal  3fab605ad041 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L111-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L111-L119

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

theorem P2M_GlobalTheory_HermFrame_posDef_blockDiagonal__3fab605ad041 {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosDef) :
    (blockDiagonal' A).PosDef := by sorry

alias «GlobalTheory».«HermFrame».«posDef_blockDiagonal'» := P2M_GlobalTheory_HermFrame_posDef_blockDiagonal__3fab605ad041
