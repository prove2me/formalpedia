-- Prove2me | Theorems.Thm_PrimeLocal_no_additive_nonintegral_j_of_fixed_prime_torsion
-- name    : PrimeLocal.no_additive_nonintegral_j_of_fixed_prime_torsion
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:15:30.919581+00:00
-- url     : https://prove2.me/theorems/0e1844db-f2be-44a3-973f-00fdf2cd891c
-- title:
--   No rational p-torsion at an additive prime with non-integral j
-- statement:
--   If an integral Weierstrass curve minimal at q has additive reduction at q with non-integral j-invariant, it has no rational point of prime order p >= 5 with p different from q.
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

namespace PrimeLocal
theorem no_additive_nonintegral_j_of_fixed_prime_torsion (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} [Fact q.Prime] (hmin : WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))) (hp : p.Prime) (hp5 : 5 ≤ p) (hqp : q ≠ p) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : (q : ℤ) ∣ W.c₄) (hj : ¬ ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) : False := by sorry
end PrimeLocal
