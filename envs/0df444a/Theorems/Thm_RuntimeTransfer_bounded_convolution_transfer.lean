-- Prove2me | Theorems.Thm_RuntimeTransfer_bounded_convolution_transfer
-- name    : RuntimeTransfer.bounded_convolution_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:48.340834+00:00
-- url     : https://prove2.me/theorems/293c9c47-8958-4b56-96e0-53b7da3f71d3
-- title:
--   Integer convolution with a proved multiplication input size
-- statement:
--   Let $r\ge1$ and let two length-$r$ integer lists have coefficient magnitudes at most $2^b$. Put $p=b+\ell(2r)$, where $\ell$ is binary magnitude length. Suppose a correct signed integer multiplier has cost at most $M(\max\{\ell(u),\ell(v)\})$ on every pair $(u,v)$, with $M$ nondecreasing. The packing program returns their coefficient convolution with accounted cost at most $E+D+M(3r(b+\ell(2r)))$. The oracle input-size bound is proved. $E,D$ remain stipulated preparation/decoding charges; their bit-machine implementation cost is not established. Magnitude length excludes a sign bit and is zero at zero.
-- source:
--   Strengthened transfer results, companion note to this mission, 24 October 2026. Concrete instruction-count and bit-length formulation of classical Bluestein and Kronecker reductions; not a claim of a new complexity exponent. Theorem 8.

import Mathlib.Order.Monotone.Basic
import Definitions.Def_RuntimeTransferPacking
import Mathlib.Data.Nat.Size
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.bounded_convolution_transfer (r b : ℕ) (a c : List ℤ)
    (ha : a.length = r) (hc : c.length = r) (hr : 1 ≤ r)
    (hab : ∀ x ∈ a, |x| ≤ 2 ^ b) (hcb : ∀ x ∈ c, |x| ≤ 2 ^ b)
    (oracle : (ℤ × ℤ) → ℤ × ℕ) (M : ℕ → ℕ) (E D : ℕ)
    (hcorrect : ∀ q, (oracle q).1 = q.1 * q.2)
    (hcost : ∀ q, (oracle q).2 ≤ M (max q.1.natAbs.size q.2.natAbs.size))
    (hM : Monotone M) :
    ((packingProgram (b + (2 * r).size) r a c E D).run oracle).1 =
      IntMul.HvdH.polyMul a c ∧
    ((packingProgram (b + (2 * r).size) r a c E D).run oracle).2 ≤
      E + D + M (3 * (b + (2 * r).size) * r) := by sorry
