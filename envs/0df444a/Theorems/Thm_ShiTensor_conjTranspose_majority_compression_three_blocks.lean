-- Prove2me | Theorems.Thm_ShiTensor_conjTranspose_majority_compression_three_blocks
-- name    : ShiTensor.conjTranspose_majority_compression_three_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T21:45:33.619825+00:00
-- url     : https://prove2.me/theorems/3c747b70-bfc2-43d4-9383-780f80c9fe8f
-- title:
--   Compressing the three-block majority polynomial along a product isometry gives the majority polynomial of the compressions
-- statement:
--   Let an operator act on a register, and let a length-preserving embedding map a smaller register into it. Place three copies of the operator on the three blocks of a threefold register, and let the threefold embedding be the product of three copies of the given one. Then compressing the inclusion-exclusion majority polynomial in the three copies along the product embedding yields the same polynomial in the three block copies of the compressed operator.
--
--   Compression does not in general commute with products of operators, and it does not commute with a square here: the compression of a square differs from the square of the compression precisely because the embedding is not invertible. What makes the majority polynomial an exception is that each of its terms is a product of copies acting on distinct blocks, so in each term at least one block is untouched, and there the embedding meets its own adjoint and the length-preserving property collapses it to the identity. This happens once in each of the three quadratic terms and not at all in the triple product, which touches every block.
--
--   The length-preserving hypothesis cannot be dropped: an embedding scaling by one half turns the left side into one sixty-fourth of the identity and the right side into five thirty-seconds of it. The purpose is to convert a statement about a spectral bound on the smaller register, where a soundness hypothesis is available, into a statement about measured acceptance on the larger one.

import Definitions.Def_ShiShallow_Matrix
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiTensor_sum_split_factor

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem conjTranspose_majority_compression_three_blocks {m w : ℕ}
    (W : Matrix (Bits m) (Bits w) ℂ)
    (hW : Matrix.conjTranspose W * W = (1 : Op w))
    (P : Op m) (A : Op w) (hA : A = Matrix.conjTranspose W * P * W)
    (Pi : Matrix (Bits (m + m + m)) (Bits (w + w + w)) ℂ)
    (hPi : Pi = Matrix.of fun (y : Bits (m + m + m)) (u : Bits (w + w + w)) =>
      W (leftBits (leftBits y)) (leftBits (leftBits u))
        * W (rightBits (leftBits y)) (rightBits (leftBits u))
        * W (rightBits y) (rightBits u))
    (P1 P2 P3 : Op (m + m + m))
    (hP1 : P1 = Matrix.of fun y z =>
      P (leftBits (leftBits y)) (leftBits (leftBits z))
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * (if rightBits y = rightBits z then 1 else 0))
    (hP2 : P2 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * P (rightBits (leftBits y)) (rightBits (leftBits z))
        * (if rightBits y = rightBits z then 1 else 0))
    (hP3 : P3 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * P (rightBits y) (rightBits z))
    (A1 A2 A3 : Op (w + w + w))
    (hA1 : A1 = Matrix.of fun y z =>
      A (leftBits (leftBits y)) (leftBits (leftBits z))
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * (if rightBits y = rightBits z then 1 else 0))
    (hA2 : A2 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * A (rightBits (leftBits y)) (rightBits (leftBits z))
        * (if rightBits y = rightBits z then 1 else 0))
    (hA3 : A3 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * A (rightBits y) (rightBits z)) :
    Matrix.conjTranspose Pi
        * (P1 * P2 + P2 * P3 + P3 * P1 - (2 : ℂ) • (P1 * P2 * P3)) * Pi
      = A1 * A2 + A2 * A3 + A3 * A1 - (2 : ℂ) • (A1 * A2 * A3) := by
  sorry

end ShiTensor
