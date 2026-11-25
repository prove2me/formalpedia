-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_mContDiffAt_blockDiagonal__bc50d51f27b0
-- name    : P2M_GlobalTheory_HermFrame_mContDiffAt_blockDiagonal__bc50d51f27b0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:18.408961+00:00
-- url     : https://prove2.me/theorems/4b12ad65-0805-4b9a-9e86-d634a42758d7
-- title:
--   P2 M Global Theory Herm Frame m Cont Diff At block Diagonal  bc50d51f27b0: P2 M Global Theory Herm Frame m Cont Diff At block Diagonal  bc50d51f27b0
-- statement:
--   The P2 M Global Theory Herm Frame m Cont Diff At block Diagonal  bc50d51f27b0 construction uses the P2 M Global Theory Herm Frame m Cont Diff At block Diagonal  bc50d51f27b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L74-L80

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
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem P2M_GlobalTheory_HermFrame_mContDiffAt_blockDiagonal__bc50d51f27b0 {k : WithTop ℕ∞} {A : ∀ i, E → Matrix (m i) (m' i) ℂ} {z : E}
    (hA : ∀ i, MContDiffAt k (A i) z) :
    MContDiffAt k (fun x => blockDiagonal' fun i => A i x) z := by sorry

alias «GlobalTheory».«HermFrame».«mContDiffAt_blockDiagonal'» := P2M_GlobalTheory_HermFrame_mContDiffAt_blockDiagonal__bc50d51f27b0
