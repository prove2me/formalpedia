-- Prove2me | Theorems.Thm_ShiShallow_exists_sum_form_eigenbasis
-- name    : ShiShallow.exists_sum_form_eigenbasis
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T01:26:13.071875+00:00
-- url     : https://prove2.me/theorems/2407ac9c-a131-4187-ba95-364454d50d03
-- title:
--   Every Hermitian matrix has an orthonormal Parseval eigenbasis, in explicit sum form
-- statement:
--   Every Hermitian matrix indexed by bit strings admits a family of amplitude arrays that is orthonormal, satisfies the Parseval identity, and consists of eigenvectors whose eigenvalues are the matrix's eigenvalues. This is the spectral theorem delivered in the explicit-sum language used by the circuit development rather than in inner-product-space language.
--
--   Stated existentially so that all of the coercion between amplitude arrays and Euclidean space stays inside the proof. It is what allows a spectral argument about a circuit's acceptance operator to proceed from Hermitian-ness alone, with no eigenbasis assumed.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem exists_sum_form_eigenbasis {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (hM : M.IsHermitian) :
    ∃ u : Bits w → (Bits w → ℂ),
      (∀ i j, (∑ y : Bits w, (starRingEnd ℂ) (u i y) * u j y) = if i = j then 1 else 0)
      ∧ (∀ z : Bits w → ℂ,
          (∑ i : Bits w, ‖∑ y : Bits w, (starRingEnd ℂ) (z y) * u i y‖ ^ 2)
            = ∑ y : Bits w, ‖z y‖ ^ 2)
      ∧ (∀ i, Matrix.mulVec M (u i)
          = fun y => ((hM.eigenvalues i : ℝ) : ℂ) * u i y) := by
  sorry

end ShiShallow
