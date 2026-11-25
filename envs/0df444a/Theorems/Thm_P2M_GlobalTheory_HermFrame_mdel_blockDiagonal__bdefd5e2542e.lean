-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_mdel_blockDiagonal__bdefd5e2542e
-- name    : P2M_GlobalTheory_HermFrame_mdel_blockDiagonal__bdefd5e2542e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:59.80488+00:00
-- url     : https://prove2.me/theorems/47af6802-a22f-4710-8d87-c606e4730b1b
-- title:
--   P2 M Global Theory Herm Frame mdel block Diagonal  bdefd5e2542e: P2 M Global Theory Herm Frame mdel block Diagonal  bdefd5e2542e
-- statement:
--   The P2 M Global Theory Herm Frame mdel block Diagonal  bdefd5e2542e construction uses the P2 M Global Theory Herm Frame mdel block Diagonal  bdefd5e2542e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L57-L62

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

theorem P2M_GlobalTheory_HermFrame_mdel_blockDiagonal__bdefd5e2542e (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdel (fun x => blockDiagonal' fun i => A i x) z ξ = blockDiagonal' fun i => mdel (A i) z ξ := by sorry

alias «GlobalTheory».«HermFrame».«mdel_blockDiagonal'» := P2M_GlobalTheory_HermFrame_mdel_blockDiagonal__bdefd5e2542e
