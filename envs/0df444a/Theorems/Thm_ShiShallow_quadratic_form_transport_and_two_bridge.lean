-- Prove2me | Theorems.Thm_ShiShallow_quadratic_form_transport_and_two_bridge
-- name    : ShiShallow.quadratic_form_transport_and_two_bridge
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T22:54:38.22236+00:00
-- url     : https://prove2.me/theorems/15d5eac5-b770-466b-80d5-1b0ac17b5350
-- title:
--   Moving a quadratic form across a rectangular matrix, and the matrix numeral two as a scalar
-- statement:
--   Two elementary facts about matrices, stated together because they are used together.
--
--   The first moves a quadratic form between registers of different sizes. Applying a rectangular matrix to a vector of the smaller register and then evaluating an operator's quadratic form on the larger register gives the same number as evaluating, on the smaller register, the quadratic form of the operator conjugated by that matrix. This is the adjoint relation for a sesquilinear pairing, and it is what allows a spectral bound established on a small register to be read as a statement about a measurement on a large one.
--
--   The second identifies the matrix numeral two, on a square matrix type, with scalar multiplication by the complex number two. Both are the operation of adding a matrix to itself, but they arise from different structures and are written differently by different results, so a statement mixing them needs the identification made explicit. Without it a bound proved with one spelling cannot be applied to a statement using the other, even though the two terms denote the same matrix.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

open ShiShallow

theorem quadratic_form_transport_and_two_bridge {M N : ℕ} :
    (∀ (Q : Matrix (Bits M) (Bits N) ℂ) (X : Op M) (psi : QState N),
        (∑ y : Bits M, (starRingEnd ℂ) (Matrix.mulVec Q psi y)
              * Matrix.mulVec X (Matrix.mulVec Q psi) y).re
          = (∑ u : Bits N, (starRingEnd ℂ) (psi u)
              * Matrix.mulVec (Matrix.conjTranspose Q * X * Q) psi u).re)
      ∧ (∀ X : Op N, (2 : Op N) * X = (2 : ℂ) • X) := by
  sorry

end ShiShallow
