-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_posSemidef_blockDiagonal__a5251a6bbb88
-- name    : P2M_GlobalTheory_HermFrame_posSemidef_blockDiagonal__a5251a6bbb88
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:00.354874+00:00
-- url     : https://prove2.me/theorems/c9398a53-2fc1-43ad-a0c8-c286306e2342
-- title:
--   P2 M Global Theory Herm Frame pos Semidef block Diagonal  a5251a6bbb88: P2 M Global Theory Herm Frame pos Semidef block Diagonal  a5251a6bbb88
-- statement:
--   The P2 M Global Theory Herm Frame pos Semidef block Diagonal  a5251a6bbb88 construction uses the P2 M Global Theory Herm Frame pos Semidef block Diagonal  a5251a6bbb88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L99-L104

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

theorem P2M_GlobalTheory_HermFrame_posSemidef_blockDiagonal__a5251a6bbb88 {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosSemidef) :
    (blockDiagonal' A).PosSemidef := by sorry

alias «GlobalTheory».«HermFrame».«posSemidef_blockDiagonal'» := P2M_GlobalTheory_HermFrame_posSemidef_blockDiagonal__a5251a6bbb88
