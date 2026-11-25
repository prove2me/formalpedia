-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IsLogBounded_toBlocks___f2ef8e35587e
-- name    : P2M_GlobalTheory_IsLogBounded_toBlocks___f2ef8e35587e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:56.274522+00:00
-- url     : https://prove2.me/theorems/df52207a-cb6b-5f85-a8a8-ff21a7f2306d
-- title:
--   P2 M Global Theory Is Log Bounded to Blocks   f2ef8e35587e: P2 M Global Theory Is Log Bounded to Blocks   f2ef8e35587e
-- statement:
--   The P2 M Global Theory Is Log Bounded to Blocks   f2ef8e35587e construction uses the P2 M Global Theory Is Log Bounded to Blocks   f2ef8e35587e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L656-L658
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L656-L658

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
open GlobalTheory.IsLogBounded

theorem P2M_GlobalTheory_IsLogBounded_toBlocks___f2ef8e35587e {G : X → Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => (G x).toBlocks₁₁ := by sorry

alias «GlobalTheory».«IsLogBounded».«toBlocks₁₁» := P2M_GlobalTheory_IsLogBounded_toBlocks___f2ef8e35587e
