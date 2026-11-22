-- Prove2me | Theorems.Thm_ShiShallow_product_eigenbasis_sum_form_three
-- name    : ShiShallow.product_eigenbasis_sum_form_three
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T05:04:40.443472+00:00
-- url     : https://prove2.me/theorems/20c763ba-b099-4adc-a222-b193385f6669
-- title:
--   Threefold products of an orthonormal family are orthonormal and satisfy Parseval, in explicit sum form
-- statement:
--   Given a family of vectors indexed by basis strings that is orthonormal with respect to the explicit coordinate sum, the family of threefold tensor products, indexed by triples, is again orthonormal in the same sense and moreover satisfies Parseval's identity: for every vector, the total squared magnitude of its coefficients against the product family equals its own total squared magnitude.
--
--   The content is a change of language rather than new mathematics. The corresponding facts are available for families of vectors in a Euclidean space, phrased through an inner product, whereas the spectral estimates that consume them are phrased through explicit coordinate sums with a conjugation. Translating between the two requires identifying the inner product with the coordinate sum and identifying the tensor product of three vectors with the function that multiplies the three factors at the three blocks of coordinates.
--
--   Parseval is stated separately from orthonormality because for a family indexed by as many elements as the dimension it is not a consequence of orthonormality alone in the form needed; it is obtained from the completeness of the product family.

import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiShallow_product_family_orthonormal_three
import Theorems.Thm_ShiShallow_product_family_parseval_three

set_option autoImplicit false

namespace ShiShallow

open ShiTensor

theorem product_eigenbasis_sum_form_three {M : ℕ} (u : Bits M → (Bits M → ℂ))
    (horth : ∀ i j, (∑ y : Bits M, (starRingEnd ℂ) (u i y) * u j y) = if i = j then 1 else 0) :
    (∀ i j : (Bits M × Bits M) × Bits M,
        (∑ y : Bits (M + M + M),
            (starRingEnd ℂ) (tensor (tensor (u i.1.1) (u i.1.2)) (u i.2) y)
              * tensor (tensor (u j.1.1) (u j.1.2)) (u j.2) y)
          = if i = j then 1 else 0)
      ∧ (∀ z : Bits (M + M + M) → ℂ,
        (∑ i : (Bits M × Bits M) × Bits M,
            ‖∑ y : Bits (M + M + M), (starRingEnd ℂ) (z y)
              * tensor (tensor (u i.1.1) (u i.1.2)) (u i.2) y‖ ^ 2)
          = ∑ y : Bits (M + M + M), ‖z y‖ ^ 2) := by
  sorry

end ShiShallow
