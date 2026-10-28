-- Prove2me | Theorems.Thm_RuntimeTransfer_full_product_middle
-- name    : RuntimeTransfer.full_product_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:29.173973+00:00
-- url     : https://prove2.me/theorems/e11d9e30-875d-4d0b-8689-39c82aeb288a
-- title:
--   Full polynomial multiplication supplies the middle product
-- statement:
--   For every natural $n$, the middle $n$ coefficients, numbered $n$ through $2n-1$, of the defined full product of complex arrays of lengths $n$ and $2n+1$ equal their middle product. Includes the empty array. No runtime claim.
-- source:
--   Strengthened transfer results, companion note to this mission, 24 October 2026. Concrete instruction-count and bit-length formulation of classical Bluestein and Kronecker reductions; not a claim of a new complexity exponent. Theorem 5, coefficient-selection identity.

import Definitions.Def_RuntimeTransferArithmetic
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.full_product_middle {n : ℕ} (q : FourierQuery n) :
    productMiddle (fullProduct q) = middleProduct q := by sorry
