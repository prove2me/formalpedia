-- Prove2me | Theorems.Thm_ShiShallow_eigenvalues_nonneg_of_quadratic_form_nonneg
-- name    : ShiShallow.eigenvalues_nonneg_of_quadratic_form_nonneg
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T01:26:20.164613+00:00
-- url     : https://prove2.me/theorems/872f4302-0a83-4800-8e94-759030a9a9c6
-- title:
--   A nonnegative quadratic form has nonnegative eigenvalues
-- statement:
--   If the quadratic form of a Hermitian matrix is nonnegative at every vector, then every eigenvalue of that matrix is nonnegative. Evaluating the hypothesis at an eigenvector turns the quadratic form into the eigenvalue itself. This is the companion of the corresponding upper bound and together they confine the spectrum to an interval, which is what a spectral amplification argument consumes.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem eigenvalues_nonneg_of_quadratic_form_nonneg {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (hM : M.IsHermitian)
    (hb : ∀ v : Bits w → ℂ,
      0 ≤ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec M v y).re)
    (i : Bits w) :
    0 ≤ hM.eigenvalues i := by
  sorry

end ShiShallow
