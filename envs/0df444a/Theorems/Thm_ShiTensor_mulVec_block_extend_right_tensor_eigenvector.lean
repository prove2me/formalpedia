-- Prove2me | Theorems.Thm_ShiTensor_mulVec_block_extend_right_tensor_eigenvector
-- name    : ShiTensor.mulVec_block_extend_right_tensor_eigenvector
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-16T01:29:05.438676+00:00
-- url     : https://prove2.me/theorems/1a1ceb54-cd6d-4b82-b77e-cb909026abbf
-- title:
--   Right-block lifting preserves tensor eigenvectors
-- statement:
--   Take a two-block register and lift an operator so that it acts on the RIGHT block while the left block is left alone: the lifted matrix has entry A (rightBits y) (rightBits z) when the left halves of y and z agree, and zero otherwise. If a vector on the right block is an eigenvector of A with eigenvalue alpha, then any product of an arbitrary left-block vector with that eigenvector is an eigenvector of the lifted operator, with the same eigenvalue. This is the right-block mirror of the corresponding left-block statement. Both are needed because a three-fold register decomposes so that one copy sits in a left block and the other two sit in right blocks, and a bound on each copy's operator has to be transported to the whole register.

import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiShallow_Matrix
import Theorems.Thm_ShiTensor_sum_split_factor

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem mulVec_block_extend_right_tensor_eigenvector {m p : ℕ} (A : Op p) (α : ℂ)
    (u : Bits m → ℂ) (v : Bits p → ℂ)
    (hv : ∀ b' : Bits p, ∑ b : Bits p, A b' b * v b = α * v b') :
    Matrix.mulVec
        (Matrix.of fun y z : Bits (m + p) =>
          if leftBits y = leftBits z then A (rightBits y) (rightBits z) else 0)
        (fun y => u (leftBits y) * v (rightBits y))
      = fun y => α * (u (leftBits y) * v (rightBits y)) := by
  sorry

end ShiTensor
