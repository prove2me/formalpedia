-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceConj_sum_symplCons_7f444f4725ab
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceConj_sum_symplCons_7f444f4725ab
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:07.064292+00:00
-- url     : https://prove2.me/theorems/327f79f6-e29d-4113-9eec-dc7afaf95e9a
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Conj sum sympl Cons 7f444f4725ab: P2 M Ground Theory Heights  Heights PSympl Reduce Conj sum sympl Cons 7f444f4725ab
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Conj sum sympl Cons 7f444f4725ab construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Conj sum sympl Cons 7f444f4725ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceConj.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceConj.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceConj
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
open GroundTheory.Heights₂.Heights.PSymplReduceConj

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceConj_sum_symplCons_7f444f4725ab {n : ℕ} (p q : ℝ) (w : Fin n ⊕ Fin n → ℝ)
    (F : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    ∑ x, symplCons p q w x * F x =
      p * F (Sum.inl 0) + q * F (Sum.inr 0) + ∑ y, w y * F (Sum.map Fin.succ Fin.succ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceConj».«sum_symplCons» := P2M_GroundTheory_Heights__Heights_PSymplReduceConj_sum_symplCons_7f444f4725ab
