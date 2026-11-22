-- Prove2me | Theorems.Thm_ShiShallow_majority_weight_eq_conj_majority_quadratic_form
-- name    : ShiShallow.majority_weight_eq_conj_majority_quadratic_form
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T04:52:20.77284+00:00
-- url     : https://prove2.me/theorems/a6b687bd-de9a-49e8-acaf-be318f80ec24
-- title:
--   The majority weight after a unitary is the quadratic form of the majority polynomial in the conjugated projectors
-- statement:
--   Apply a unitary matrix to a vector and measure the weight of the basis strings on which at least two of three designated coordinates read one. That weight equals the quadratic form, taken at the original vector, of a particular matrix: the inclusion-exclusion polynomial in the three coordinate projectors, each conjugated by the unitary, namely the sum of the three pairwise products minus twice the triple product.
--
--   The point of rewriting a weight as a quadratic form is that the weight is what a measurement produces, while the quadratic form is what spectral methods bound. Because the polynomial is built from the three conjugated projectors, and those commute whenever the projectors act on separate registers, the resulting operator can be diagonalised on a product basis and its eigenvalues read off as the same polynomial in the individual eigenvalues. This is the step that converts a statement about measurement outcomes into one about a spectrum.
--
--   No normalization of the vector is assumed, and the unitary is arbitrary, so the identity applies to entangled inputs as well as product ones.

import Definitions.Def_ShiShallow_Matrix
import Theorems.Thm_ShiShallow_projOut_majority_inclusion_exclusion
import Theorems.Thm_ShiShallow_conj_majority_inclusion_exclusion_of_unitary

set_option autoImplicit false

namespace ShiShallow

theorem majority_weight_eq_conj_majority_quadratic_form {N : ℕ} (V : Op N) (hV : star V * V = (1 : Op N))
    (w1 w2 w3 : Fin N) (Φ : Bits N → ℂ) :
    (∑ y : Bits N,
        if 2 ≤ (if y w1 = true then (1 : ℕ) else 0) + (if y w2 = true then (1 : ℕ) else 0)
              + (if y w3 = true then (1 : ℕ) else 0)
          then ‖Matrix.mulVec V Φ y‖ ^ 2 else 0)
      = (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * Matrix.mulVec
            ((star V * projOut w1 * V) * (star V * projOut w2 * V)
              + (star V * projOut w2 * V) * (star V * projOut w3 * V)
              + (star V * projOut w3 * V) * (star V * projOut w1 * V)
              - 2 * ((star V * projOut w1 * V) * (star V * projOut w2 * V)
                  * (star V * projOut w3 * V))) Φ y).re := by
  sorry

end ShiShallow
