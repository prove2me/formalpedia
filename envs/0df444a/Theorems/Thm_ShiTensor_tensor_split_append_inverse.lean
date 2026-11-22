-- Prove2me | Theorems.Thm_ShiTensor_tensor_split_append_inverse
-- name    : ShiTensor.tensor_split_append_inverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T05:06:41.785246+00:00
-- url     : https://prove2.me/theorems/61c0e3a6-4018-4538-8c86-d3eb665bb71c
-- title:
--   leftBits/rightBits are inverse to Fin.append
-- statement:
--   leftBits and rightBits are mutually inverse to Fin.append: reading off the two halves of Fin.append a b recovers a and b, and re-appending the halves of any y recovers y.
--
--   Together these say that y |-> (leftBits y, rightBits y) is a bijection Bits (m + p) ~= Bits m x Bits p. That is precisely the fact the ShiTensor_Core module docstring flags as NOT proved in the bundle (its limitation 2), and it is what every reindexing argument over a joint index needs.
--
--   SCOPE. Pure index bookkeeping over Fin.castAdd / Fin.natAdd. No amplitudes, no normalisation, and no connection to circuit dynamics. The splitting is positional: it is tied to the specific m + p decomposition and no commutativity or associativity is claimed.

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

open ShiShallow

namespace ShiTensor

theorem tensor_split_append_inverse {m p : ℕ} :
    (∀ (a : Bits m) (b : Bits p), leftBits (Fin.append a b) = a) ∧
    (∀ (a : Bits m) (b : Bits p), rightBits (Fin.append a b) = b) ∧
    (∀ (y : Bits (m + p)), Fin.append (leftBits y) (rightBits y) = y) := by
  sorry

end ShiTensor
