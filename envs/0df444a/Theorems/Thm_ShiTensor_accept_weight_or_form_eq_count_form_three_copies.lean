-- Prove2me | Theorems.Thm_ShiTensor_accept_weight_or_form_eq_count_form_three_copies
-- name    : ShiTensor.accept_weight_or_form_eq_count_form_three_copies
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T02:43:24.874125+00:00
-- url     : https://prove2.me/theorems/14669888-bc13-44f3-a5e0-e5a2b33e05b8
-- title:
--   The two standard spellings of the three-copy majority accept weight agree
-- statement:
--   The weight that a threefold tensor product of a state assigns to the basis strings on which the majority of three designated wires read one is the same whether it is written in either of two conventions, and the identity holds for an arbitrary state with no normalization assumed.
--
--   The two conventions differ in three independent ways, all of which the statement reconciles at once. The three blocks of wires may be grouped to the left or to the right, and the two groupings are not interchangeable without a reindexing, since associativity of addition on the natural numbers is a theorem rather than a definitional identity. The wire addresses may be written as explicit injections into the combined register or as iterated projections onto the left and right halves. And the majority condition may be written as the disjunction of the three pairwise conjunctions or as the statement that at least two of three indicators sum to two or more.
--
--   The purpose is to let a statement about what the amplified circuit computes be composed with a statement about the resulting probability, when the two were proved in different conventions.

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem accept_weight_or_form_eq_count_form_three_copies {M : ℕ} (out : Fin M) (A : QState M) :
    (∑ v : Bits (M + M + M),
        if ((v (Fin.castAdd M (Fin.castAdd M out)) && v (Fin.castAdd M (Fin.natAdd M out)))
            || ((v (Fin.castAdd M (Fin.natAdd M out)) && v (Fin.natAdd (M + M) out))
              || (v (Fin.castAdd M (Fin.castAdd M out)) && v (Fin.natAdd (M + M) out))))
        then ‖tensor (tensor A A) A v‖ ^ 2 else 0)
      = ∑ y : Bits (M + (M + M)),
          (if 2 ≤ (if leftBits y out then (1 : ℕ) else 0)
                + (if leftBits (rightBits y) out then (1 : ℕ) else 0)
                + (if rightBits (rightBits y) out then (1 : ℕ) else 0)
            then ‖tensor A (tensor A A) y‖ ^ 2 else 0) := by
  sorry

end ShiTensor
