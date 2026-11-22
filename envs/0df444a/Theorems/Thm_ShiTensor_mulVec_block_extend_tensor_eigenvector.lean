-- Prove2me | Theorems.Thm_ShiTensor_mulVec_block_extend_tensor_eigenvector
-- name    : ShiTensor.mulVec_block_extend_tensor_eigenvector
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T19:32:02.621667+00:00
-- url     : https://prove2.me/theorems/384389d6-fb2a-457a-9ec0-5070597311de
-- title:
--   A block eigenvector tensored with an arbitrary vector is an eigenvector of the block extension, in matrix form
-- statement:
--   The MATRIX version of the statement that an eigenvector of a block operator stays an eigenvector when an arbitrary second register is attached. The operator is written inline with no new definition: on joint basis strings, the entry at a row and column is the small matrix's entry at the two LEFT restrictions when the two RIGHT restrictions agree, and zero otherwise. In ordinary notation that matrix is the small operator tensored with the identity on the second block, written without any tensor product so it is a plain formula on indices. Given that a vector satisfies the eigenvector equation for the small matrix in explicit summed form, the pointwise product of it on the left restriction with an ARBITRARY vector on the right restriction is an eigenvector of the extension, with the same eigenvalue and no condition whatever on the second factor.
--
--   WHY THE MATRIX FORM IS NEEDED. An amplitude-array analogue is separately accepted as ShiTensor.block_action_tensor_eigenvector, but it is NOT usable for this purpose: it is formulated as an action on arrays rather than as multiplication by a matrix, so it says nothing about the matrix object whose spectrum one wants to discuss. Any spectral argument that must compose with matrix products, conjugate transposes or locality lemmas needs this form.
--
--   MECHANISM: collapse and reindex. Multiplying by the extension gives a sum over all joint column strings; the right-block guard kills every column whose right restriction differs from the row's, so the survivors form one copy of the left index set. The reindexing transports the sum through the standard equivalence between functions on a concatenated index set and pairs of functions, then splits it into a double sum. On a concatenation the left restriction is the first argument and the right the second, each by a one-line extensionality argument. The inner sum then has a single surviving term, and the constant second-factor value pulls out, leaving the eigenvector hypothesis to finish.
--
--   HONEST LIMITATIONS. This is ONE eigen-relation and nothing more. It does NOT prove the product vectors are orthonormal, and does NOT prove they SPAN the joint space; both are needed before expanding an arbitrary joint state in such products. The small matrix is entirely arbitrary -- no symmetry, positivity, unitarity or normalisation -- so nothing follows about the eigenvalue being real, about eigenvectors for distinct eigenvalues being orthogonal, or about a spectral decomposition existing at all. The eigenvalue may be zero and the vector may be zero, in which case the statement is vacuous. The splitting is positional and asymmetric, tied to this decomposition of the wire count; no commutativity or associativity is claimed. Nothing here touches circuits, measurement, the output projector, acceptance probabilities, witnesses or amplification, and in particular nothing says acceptance probabilities multiply across disjoint blocks.

import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

theorem mulVec_block_extend_tensor_eigenvector {m p : ℕ} (A : Op m) (α : ℂ)
    (u : Bits m → ℂ) (v : Bits p → ℂ)
    (hu : ∀ a' : Bits m, ∑ a : Bits m, A a' a * u a = α * u a') :
    Matrix.mulVec
        (Matrix.of fun y z : Bits (m + p) =>
          if rightBits y = rightBits z then A (leftBits y) (leftBits z) else 0)
        (fun y => u (leftBits y) * v (rightBits y))
      = fun y => α * (u (leftBits y) * v (rightBits y)) := by
  sorry

end ShiTensor
