-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IsLogBounded_schurComplement___1e40d9598789
-- name    : P2M_GlobalTheory_IsLogBounded_schurComplement___1e40d9598789
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:28.710806+00:00
-- url     : https://prove2.me/theorems/2495de00-d36e-4d79-aae0-f0ce6448e206
-- title:
--   P2 M Global Theory Is Log Bounded schur Complement   1e40d9598789: P2 M Global Theory Is Log Bounded schur Complement   1e40d9598789
-- statement:
--   The P2 M Global Theory Is Log Bounded schur Complement   1e40d9598789 construction uses the P2 M Global Theory Is Log Bounded schur Complement   1e40d9598789 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L904-L906
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L904-L906

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
variable [Fintype n]
open GlobalTheory.IsLogBounded
variable [Fintype m]

theorem P2M_GlobalTheory_IsLogBounded_schurComplement___1e40d9598789 {G : X → Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => schurComplement₂₂ (G x) := by sorry

alias «GlobalTheory».«IsLogBounded».«schurComplement₂₂» := P2M_GlobalTheory_IsLogBounded_schurComplement___1e40d9598789
