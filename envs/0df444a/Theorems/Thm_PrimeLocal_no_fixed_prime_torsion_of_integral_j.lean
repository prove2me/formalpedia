-- Prove2me | Theorems.Thm_PrimeLocal_no_fixed_prime_torsion_of_integral_j
-- name    : PrimeLocal.no_fixed_prime_torsion_of_integral_j
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:13:01.502787+00:00
-- url     : https://prove2.me/theorems/6ca1fde1-78c7-4b8d-b3e8-174a0c5e2d8c
-- title:
--   No rational p-torsion with integral j at an additive prime 2 or 3 (boundary)
-- statement:
--   Boundary statement of the local package: with integral j-invariant at the relevant prime, a rational point of prime order p >= 23 is excluded by the Frobenius fixed-abscissa count p - 1 <= 2q.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
open IsLocalRing ValuationSubring

namespace PrimeLocal
theorem no_fixed_prime_torsion_of_integral_j (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) (hcount : 2 * q < p - 1) (hj : ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : False := by sorry
end PrimeLocal
