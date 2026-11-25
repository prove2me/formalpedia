-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_mdbar_blockDiagonal__573a2ef87000
-- name    : P2M_GlobalTheory_HermFrame_mdbar_blockDiagonal__573a2ef87000
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:19.23926+00:00
-- url     : https://prove2.me/theorems/bf22d82c-e8a8-4988-9b5a-973599db4305
-- title:
--   P2 M Global Theory Herm Frame mdbar block Diagonal  573a2ef87000: P2 M Global Theory Herm Frame mdbar block Diagonal  573a2ef87000
-- statement:
--   The P2 M Global Theory Herm Frame mdbar block Diagonal  573a2ef87000 construction uses the P2 M Global Theory Herm Frame mdbar block Diagonal  573a2ef87000 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L64-L70

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

theorem P2M_GlobalTheory_HermFrame_mdbar_blockDiagonal__573a2ef87000 (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdbar (fun x => blockDiagonal' fun i => A i x) z ξ =
      blockDiagonal' fun i => mdbar (A i) z ξ := by sorry

alias «GlobalTheory».«HermFrame».«mdbar_blockDiagonal'» := P2M_GlobalTheory_HermFrame_mdbar_blockDiagonal__573a2ef87000
