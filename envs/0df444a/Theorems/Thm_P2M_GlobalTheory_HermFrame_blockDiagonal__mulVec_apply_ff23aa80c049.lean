-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_blockDiagonal__mulVec_apply_ff23aa80c049
-- name    : P2M_GlobalTheory_HermFrame_blockDiagonal__mulVec_apply_ff23aa80c049
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:55.854472+00:00
-- url     : https://prove2.me/theorems/202aefdb-a6f1-480d-93ae-03029aa18dc3
-- title:
--   P2 M Global Theory Herm Frame block Diagonal  mul Vec apply ff23aa80c049: P2 M Global Theory Herm Frame block Diagonal  mul Vec apply ff23aa80c049
-- statement:
--   The P2 M Global Theory Herm Frame block Diagonal  mul Vec apply ff23aa80c049 construction uses the P2 M Global Theory Herm Frame block Diagonal  mul Vec apply ff23aa80c049 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L86-L92

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
omit [∀ i, Fintype (m' i)]

theorem P2M_GlobalTheory_HermFrame_blockDiagonal__mulVec_apply_ff23aa80c049 (T : ∀ i, Matrix (m' i) (m i) ℂ) (v : (Σ i, m i) → ℂ) (i : o)
    (a : m' i) : (blockDiagonal' T *ᵥ v) ⟨i, a⟩ = (T i *ᵥ fun b => v ⟨i, b⟩) a := by sorry

alias «GlobalTheory».«HermFrame».«blockDiagonal'_mulVec_apply» := P2M_GlobalTheory_HermFrame_blockDiagonal__mulVec_apply_ff23aa80c049
