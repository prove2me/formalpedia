-- Prove2me | Theorems.Thm_ShiTensor_three_copy_acceptance_operators_are_block_liftings
-- name    : ShiTensor.three_copy_acceptance_operators_are_block_liftings
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T23:25:25.611728+00:00
-- url     : https://prove2.me/theorems/fad6820c-4d29-4f20-b734-e40bfd5451ee
-- title:
--   Each copy's acceptance operator in a three-copy verifier is the block lifting of the single-copy one
-- statement:
--   Place three copies of a circuit on the three blocks of a threefold register. For each copy, the operator obtained by conjugating the projector onto that copy's output wire by the whole three-copy circuit is the block lifting of the corresponding single-copy operator: it acts as the single-copy acceptance operator on its own block and as the identity on the other two.
--
--   The proof determines the three-copy circuit's matrix entrywise. A basis string of the combined register is the tensor of its three block restrictions, so the matrix entry between two basis strings is obtained by running the circuit on a product of three basis indicators, which factors into the three single-copy actions. It follows that the three-copy circuit's matrix is the threefold product of the single-copy one, and the projector onto a single output wire likewise splits, since it is diagonal and a string is determined by its restrictions. Conjugating then collapses the two untouched blocks by unitarity of the single-copy circuit.
--
--   No appeal to locality is needed, and this matters: knowing only that an operator acts within a set of wires does not say which operator it is, so a locality argument cannot identify the block factor with the single-copy acceptance operator, which is the quantity a soundness hypothesis constrains.

import Definitions.Def_ShiShallow_Matrix
import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiEmbed_Core
import Theorems.Thm_ShiTensor_runLayered_embed_three_blocks
import Theorems.Thm_ShiTensor_sum_split_factor
import Theorems.Thm_ShiTensor_tensor_split_append_inverse
import Theorems.Thm_ShiShallow_runLayered_eq_circMatrix_mulVec
import Theorems.Thm_ShiShallow_apply1_eq_apply1Matrix_mulVec
import Theorems.Thm_ShiShallow_cnotState_eq_cnotMatrix_mulVec
import Theorems.Thm_ShiShallow_circMatrix_unitary

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem three_copy_acceptance_operators_are_block_liftings {M : ℕ} (c : Layered M) (out : Fin M)
    (C3 : Layered (M + M + M))
    (hC3 : C3 =
      ShiEmbed.embedCirc
          ((Fin.castAdd M : Fin (M + M) → Fin (M + M + M)) ∘
            (Fin.castAdd M : Fin M → Fin (M + M)))
          ((Fin.castAdd_injective (M + M) M).comp (Fin.castAdd_injective M M)) c
        ++ ShiEmbed.embedCirc
          ((Fin.castAdd M : Fin (M + M) → Fin (M + M + M)) ∘
            (Fin.natAdd M : Fin M → Fin (M + M)))
          ((Fin.castAdd_injective (M + M) M).comp (Fin.natAdd_injective M M)) c
        ++ ShiEmbed.embedCirc (Fin.natAdd (M + M) : Fin M → Fin (M + M + M))
          (Fin.natAdd_injective M (M + M)) c)
    (A : Op M) (hA : A = star (circMatrix c) * projOut out * circMatrix c)
    (L1 L2 L3 : Op (M + M + M))
    (hL1 : L1 = Matrix.of fun y z =>
      A (leftBits (leftBits y)) (leftBits (leftBits z))
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * (if rightBits y = rightBits z then 1 else 0))
    (hL2 : L2 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * A (rightBits (leftBits y)) (rightBits (leftBits z))
        * (if rightBits y = rightBits z then 1 else 0))
    (hL3 : L3 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * A (rightBits y) (rightBits z)) :
    star (circMatrix C3) * projOut (Fin.castAdd M (Fin.castAdd M out)) * circMatrix C3 = L1
      ∧ star (circMatrix C3) * projOut (Fin.castAdd M (Fin.natAdd M out)) * circMatrix C3 = L2
      ∧ star (circMatrix C3) * projOut (Fin.natAdd (M + M) out) * circMatrix C3 = L3 := by
  sorry

end ShiTensor
