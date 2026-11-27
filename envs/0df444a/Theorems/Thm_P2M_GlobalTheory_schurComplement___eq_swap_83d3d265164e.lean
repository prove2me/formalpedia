-- Prove2me | Theorems.Thm_P2M_GlobalTheory_schurComplement___eq_swap_83d3d265164e
-- name    : P2M_GlobalTheory_schurComplement___eq_swap_83d3d265164e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:38.768155+00:00
-- url     : https://prove2.me/theorems/1c9c6a74-b7d1-4ead-a067-d0db58a76f3c
-- title:
--   P2 M Global Theory schur Complement   eq swap 83d3d265164e: P2 M Global Theory schur Complement   eq swap 83d3d265164e
-- statement:
--   The P2 M Global Theory schur Complement   eq swap 83d3d265164e construction uses the P2 M Global Theory schur Complement   eq swap 83d3d265164e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L479-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L479-L481

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
variable {m n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype m] [DecidableEq m]
omit [DecidableEq m] [Fintype m]

theorem P2M_GlobalTheory_schurComplement___eq_swap_83d3d265164e (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    schurComplement₂₂ G = schurComplement₁₁ (G.submatrix Sum.swap Sum.swap) := by sorry

alias «GlobalTheory».«schurComplement₂₂_eq_swap» := P2M_GlobalTheory_schurComplement___eq_swap_83d3d265164e
