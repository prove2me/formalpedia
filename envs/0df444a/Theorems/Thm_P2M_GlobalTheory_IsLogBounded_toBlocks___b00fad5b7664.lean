-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IsLogBounded_toBlocks___b00fad5b7664
-- name    : P2M_GlobalTheory_IsLogBounded_toBlocks___b00fad5b7664
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:27.47486+00:00
-- url     : https://prove2.me/theorems/3923adb5-2ab1-4ae7-ad6e-2fcccd9a5a35
-- title:
--   P2 M Global Theory Is Log Bounded to Blocks   b00fad5b7664: P2 M Global Theory Is Log Bounded to Blocks   b00fad5b7664
-- statement:
--   The P2 M Global Theory Is Log Bounded to Blocks   b00fad5b7664 construction uses the P2 M Global Theory Is Log Bounded to Blocks   b00fad5b7664 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L660-L662
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L660-L662

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

theorem P2M_GlobalTheory_IsLogBounded_toBlocks___b00fad5b7664 {G : X → Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => (G x).toBlocks₂₂ := by sorry

alias «GlobalTheory».«IsLogBounded».«toBlocks₂₂» := P2M_GlobalTheory_IsLogBounded_toBlocks___b00fad5b7664
