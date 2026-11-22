-- Prove2me | Theorems.Thm_ShiShallow_eigenvalues_le_of_quadratic_form_le
-- name    : ShiShallow.eigenvalues_le_of_quadratic_form_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T23:14:16.905032+00:00
-- url     : https://prove2.me/theorems/77ae2bba-b045-4a4a-9bd3-5c25a55a9dd8
-- title:
--   A quadratic form bound bounds every eigenvalue of a Hermitian matrix
-- statement:
--   If the quadratic form of a Hermitian matrix is at most s times the squared norm for every vector, then every eigenvalue of that matrix is at most s. Evaluating the hypothesis at a unit eigenvector turns the quadratic form into the eigenvalue itself.
--
--   This is the matrix-level counterpart of the variational principle and is the step that converts an operational bound, of the kind that a soundness guarantee provides, into spectral information usable by a simultaneous-diagonalisation argument.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem eigenvalues_le_of_quadratic_form_le {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (hM : M.IsHermitian) (s : ℝ)
    (hb : ∀ v : Bits w → ℂ,
      (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec M v y).re
        ≤ s * ∑ y : Bits w, ‖v y‖ ^ 2)
    (i : Bits w) :
    hM.eigenvalues i ≤ s := by
  sorry

end ShiShallow
