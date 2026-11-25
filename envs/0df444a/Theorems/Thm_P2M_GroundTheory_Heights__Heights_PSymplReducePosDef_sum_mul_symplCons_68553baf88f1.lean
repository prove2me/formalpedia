-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReducePosDef_sum_mul_symplCons_68553baf88f1
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReducePosDef_sum_mul_symplCons_68553baf88f1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:08.054927+00:00
-- url     : https://prove2.me/theorems/660b6009-29b5-496e-9cdd-7fd7dfdcd089
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Pos Def sum mul sympl Cons 68553baf88f1: P2 M Ground Theory Heights  Heights PSympl Reduce Pos Def sum mul sympl Cons 68553baf88f1
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Pos Def sum mul sympl Cons 68553baf88f1 construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Pos Def sum mul sympl Cons 68553baf88f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReducePosDef.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReducePosDef.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReducePosDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.PSymplReducePosDef

theorem P2M_GroundTheory_Heights__Heights_PSymplReducePosDef_sum_mul_symplCons_68553baf88f1 {n : ℕ} (c : ℝ) (x : Fin n ⊕ Fin n → ℝ)
    (F : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    ∑ p, F p * symplCons c 0 x p =
      F (Sum.inl 0) * c + ∑ q, F (Sum.map Fin.succ Fin.succ q) * x q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReducePosDef».«sum_mul_symplCons» := P2M_GroundTheory_Heights__Heights_PSymplReducePosDef_sum_mul_symplCons_68553baf88f1
