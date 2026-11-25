-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_form_blockDiagonal__1704ae5cb2fa
-- name    : P2M_GlobalTheory_HermFrame_form_blockDiagonal__1704ae5cb2fa
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:13.336496+00:00
-- url     : https://prove2.me/theorems/7f7b371f-dd4c-44fe-b21e-eb8c203e138e
-- title:
--   P2 M Global Theory Herm Frame form block Diagonal  1704ae5cb2fa: P2 M Global Theory Herm Frame form block Diagonal  1704ae5cb2fa
-- statement:
--   The P2 M Global Theory Herm Frame form block Diagonal  1704ae5cb2fa construction uses the P2 M Global Theory Herm Frame form block Diagonal  1704ae5cb2fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L94-L97

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

theorem P2M_GlobalTheory_HermFrame_form_blockDiagonal__1704ae5cb2fa (A : ∀ i, Matrix (m i) (m i) ℂ) (v w : (Σ i, m i) → ℂ) :
    form (blockDiagonal' A) v w = ∑ i, form (A i) (fun a => v ⟨i, a⟩) fun a => w ⟨i, a⟩ := by sorry

alias «GlobalTheory».«HermFrame».«form_blockDiagonal'» := P2M_GlobalTheory_HermFrame_form_blockDiagonal__1704ae5cb2fa
