-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_IwahoriEntryBound_main
-- name    : UpperTheory.Reformulated.B.IwahoriEntryBound.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:00.057264+00:00
-- url     : https://prove2.me/theorems/415e7f19-984b-4f65-b428-bddd07ea61a3
-- title:
--   Iwahori Entry Bound: main
-- statement:
--   The Iwahori Entry Bound construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IwahoriEntryBound.lean#L59-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IwahoriEntryBound.lean#L59-L103

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IwahoriEntryBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers

theorem UpperTheory.Reformulated.B.IwahoriEntryBound.main :
    ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {g : GL (Fin n) L},
      g ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n →
        ∀ (i : Fin n),
          (Valued.v : L → WithZero (Multiplicative ℤ)) ((↑g : Matrix (Fin n) (Fin n) L) i i) =
            (1 : WithZero (Multiplicative ℤ)) := by sorry
