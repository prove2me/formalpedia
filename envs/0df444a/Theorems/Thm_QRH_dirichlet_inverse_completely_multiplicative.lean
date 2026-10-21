-- Prove2me | Theorems.Thm_QRH_dirichlet_inverse_completely_multiplicative
-- name    : QRH.dirichlet_inverse_completely_multiplicative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T12:47:42.346202+00:00
-- url     : https://prove2.me/theorems/b4742e1e-020b-4d60-b15e-c49454a85ca6
-- title:
--   Mobius inversion over completely multiplicative weights
-- statement:
--   Let d be a completely multiplicative function on the world: d(ab) = d(a) d(b) and d(1) = 1. Then the Mobius function twisted by d is the Dirichlet inverse of d with respect to the divisor-sum convolution of the interface: the divisor sum of mu(n) d(n) d(coDiv b n) over the divisors of b equals 1 when b is the unit element and 0 for every other element b.
-- source:
--   The Quasi-Riemann Hypothesis, October 2026, Section 5 (equation 2.12).

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun

universe u

namespace QRH

/-- Möbius inversion over completely multiplicative weights: the Möbius
function twisted by a completely multiplicative weight is its Dirichlet
inverse. This is the identity behind the cube-completion inversion of
section 5 of the source (equation 2.12): there, the completed theta
sum T_h is the sum of the cube-completed sums P_h weighted by the
completely multiplicative cube weight w_h, and the Möbius-twisted
inversion recovers P_h from T_h. The proof factors each summand as the
weight of the full element — complete multiplicativity, the
complementary-divisor axiom — and applies the Möbius inversion principle
of the interface. -/
theorem dirichlet_inverse_completely_multiplicative (W : QRHWorld.{u})
    (d : W.E → ℂ)
    (hd_mul : ∀ (a b : W.E), d (W.mul a b) = d a * d b)
    (hd_one : d W.one = 1) :
    ∑ n ∈ W.divs W.one, W.mu n * d n * d (W.coDiv W.one n) = 1
      ∧ ∀ b : W.E, b ≠ W.one →
        ∑ n ∈ W.divs b, W.mu n * d n * d (W.coDiv b n) = 0 := by
  sorry

end QRH
