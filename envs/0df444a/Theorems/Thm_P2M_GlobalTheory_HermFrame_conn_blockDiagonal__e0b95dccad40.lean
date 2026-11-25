-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_conn_blockDiagonal__e0b95dccad40
-- name    : P2M_GlobalTheory_HermFrame_conn_blockDiagonal__e0b95dccad40
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:08.193067+00:00
-- url     : https://prove2.me/theorems/31e8c7c3-b70a-4428-876d-95e179700781
-- title:
--   P2 M Global Theory Herm Frame conn block Diagonal  e0b95dccad40: P2 M Global Theory Herm Frame conn block Diagonal  e0b95dccad40
-- statement:
--   The P2 M Global Theory Herm Frame conn block Diagonal  e0b95dccad40 construction uses the P2 M Global Theory Herm Frame conn block Diagonal  e0b95dccad40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L131-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L131-L138

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

theorem P2M_GlobalTheory_HermFrame_conn_blockDiagonal__e0b95dccad40 (h : ∀ i, IsUnit (H i z).det) (ξ : E) :
    conn (fun x => blockDiagonal' fun i => H i x) z ξ = blockDiagonal' fun i => conn (H i) z ξ := by sorry

alias «GlobalTheory».«HermFrame».«conn_blockDiagonal'» := P2M_GlobalTheory_HermFrame_conn_blockDiagonal__e0b95dccad40
