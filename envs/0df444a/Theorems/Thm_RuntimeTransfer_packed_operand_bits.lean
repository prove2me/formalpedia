-- Prove2me | Theorems.Thm_RuntimeTransfer_packed_operand_bits
-- name    : RuntimeTransfer.packed_operand_bits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:43.255296+00:00
-- url     : https://prove2.me/theorems/c8eb6290-d3fd-433b-8f38-9e11900c7493
-- title:
--   Signed packed operands use at most $3pr$ magnitude bits
-- statement:
--   For every $p\ge1$ and integer list $a$ of length $r$ with coefficient magnitudes at most $2^p$, the signed integer obtained by packing in base $2^{3p}$ has binary magnitude length at most $3pr$. Zero has length zero and no sign bit is counted. Empty lists, signed coefficients, cancellation, and endpoint coefficients are included. No runtime is asserted.
-- source:
--   Strengthened transfer results, companion note to this mission, 24 October 2026. Concrete instruction-count and bit-length formulation of classical Bluestein and Kronecker reductions; not a claim of a new complexity exponent. Theorem 7.

import Definitions.Def_RuntimeTransferPacking
import Mathlib.Data.Nat.Size
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.packed_operand_bits (p : ℕ) (hp : 1 ≤ p) (a : List ℤ)
    (ha : ∀ x ∈ a, |x| ≤ 2 ^ p) :
    (IntMul.HvdH.kpack (2 ^ (3 * p)) a).natAbs.size ≤ 3 * p * a.length := by sorry
