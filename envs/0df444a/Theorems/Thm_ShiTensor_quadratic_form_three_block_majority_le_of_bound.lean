-- Prove2me | Theorems.Thm_ShiTensor_quadratic_form_three_block_majority_le_of_bound
-- name    : ShiTensor.quadratic_form_three_block_majority_le_of_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T20:45:56.457396+00:00
-- url     : https://prove2.me/theorems/17261a6d-d4f0-4762-b63c-92dc15fc95a7
-- title:
--   The majority of three independent copies of a bounded observable is bounded by the majority polynomial, for every state
-- statement:
--   Let a Hermitian operator on a register have the property that its quadratic form at every normalized vector lies between zero and some number at most one. Place three copies of it on three consecutive blocks of a threefold register, in the sense that a product of three eigenvectors is a common eigenvector of the three copies with the three original eigenvalues. Then the quadratic form of the inclusion-exclusion polynomial in the three copies, that is the sum of the three pairwise products minus twice the triple product, is at most the majority polynomial of the bound at every normalized state of the threefold register.
--
--   The state is arbitrary. It is not assumed to factor across the three blocks, and that is the entire content: for a product state the conclusion is elementary, since the three copies then behave independently, whereas for an entangled state it requires that the three copies commute and are therefore simultaneously diagonalised by products of eigenvectors of the original operator. The polynomial's eigenvalues on such a product are the same polynomial evaluated at the three eigenvalues, each confined to the given interval, and maximising over that cube gives the stated bound.
--
--   The operator is an arbitrary Hermitian rather than a projector, and this is essential rather than incidental. A projector's quadratic form attains one at any vector in its range, so a hypothesis bounding it below one forces the projector to vanish; the statement would then be true but empty. For a general Hermitian the hypothesis is satisfiable with room to spare, and is in fact attained with equality by a suitable multiple of the identity.

import Definitions.Def_ShiShallow_Matrix
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiShallow_exists_sum_form_eigenbasis
import Theorems.Thm_ShiShallow_eigenvalues_nonneg_of_quadratic_form_nonneg
import Theorems.Thm_ShiShallow_eigenvalues_le_of_quadratic_form_le
import Theorems.Thm_ShiShallow_product_eigenbasis_sum_form_three
import Theorems.Thm_ShiShallow_mulVec_majority_inclusion_exclusion_of_common_eigenvector
import Theorems.Thm_ShiShallow_quadratic_form_majority_le_of_eigenbasis

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem quadratic_form_three_block_majority_le_of_bound {w : ℕ} (A : Op w) (hA : A.IsHermitian) (s : ℝ) (hs : s ≤ 1)
    (hqf : ∀ v : Bits w → ℂ, (∑ y : Bits w, ‖v y‖ ^ 2) = 1 →
      0 ≤ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re
        ∧ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re ≤ s)
    (A1 A2 A3 : Op (w + w + w))
    (hlift : ∀ (p q t : QState w) (α β γ : ℂ),
      Matrix.mulVec A p = α • p → Matrix.mulVec A q = β • q → Matrix.mulVec A t = γ • t →
        Matrix.mulVec A1 (tensor (tensor p q) t) = α • tensor (tensor p q) t
          ∧ Matrix.mulVec A2 (tensor (tensor p q) t) = β • tensor (tensor p q) t
          ∧ Matrix.mulVec A3 (tensor (tensor p q) t) = γ • tensor (tensor p q) t)
    (Θ : QState (w + w + w)) (hΘ : (∑ y : Bits (w + w + w), ‖Θ y‖ ^ 2) = 1) :
    (∑ y : Bits (w + w + w), (starRingEnd ℂ) (Θ y)
        * Matrix.mulVec (A1 * A2 + A2 * A3 + A3 * A1 - (2 : ℂ) • (A1 * A2 * A3)) Θ y).re
      ≤ 3 * s ^ 2 - 2 * s ^ 3 := by
  sorry

end ShiTensor
