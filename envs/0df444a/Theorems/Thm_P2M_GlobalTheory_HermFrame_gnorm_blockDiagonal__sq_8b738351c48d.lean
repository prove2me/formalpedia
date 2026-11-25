-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_gnorm_blockDiagonal__sq_8b738351c48d
-- name    : P2M_GlobalTheory_HermFrame_gnorm_blockDiagonal__sq_8b738351c48d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:08.371116+00:00
-- url     : https://prove2.me/theorems/15e3fa2e-8415-419d-a11c-5cc8f9a23372
-- title:
--   P2 M Global Theory Herm Frame gnorm block Diagonal  sq 8b738351c48d: P2 M Global Theory Herm Frame gnorm block Diagonal  sq 8b738351c48d
-- statement:
--   The P2 M Global Theory Herm Frame gnorm block Diagonal  sq 8b738351c48d construction uses the P2 M Global Theory Herm Frame gnorm block Diagonal  sq 8b738351c48d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L106-L109

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

theorem P2M_GlobalTheory_HermFrame_gnorm_blockDiagonal__sq_8b738351c48d {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosSemidef)
    (v : (Σ i, m i) → ℂ) :
    gnorm (blockDiagonal' A) v ^ 2 = ∑ i, gnorm (A i) (fun a => v ⟨i, a⟩) ^ 2 := by sorry

alias «GlobalTheory».«HermFrame».«gnorm_blockDiagonal'_sq» := P2M_GlobalTheory_HermFrame_gnorm_blockDiagonal__sq_8b738351c48d
