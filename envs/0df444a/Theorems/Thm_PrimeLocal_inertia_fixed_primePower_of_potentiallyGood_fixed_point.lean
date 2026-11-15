-- Prove2me | Theorems.Thm_PrimeLocal_inertia_fixed_primePower_of_potentiallyGood_fixed_point
-- name    : PrimeLocal.inertia_fixed_primePower_of_potentiallyGood_fixed_point
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:49:24.675197+00:00
-- url     : https://prove2.me/theorems/aa886eed-d17e-49f8-89e1-6c6ae50e60ce
-- title:
--   Inertia fixes p-power torsion at a potentially good prime
-- statement:
--   If the curve has potentially good reduction at q (integral j) and q differs from p, inertia at q fixes the p-power torsion, under the fixed-point hypothesis of the local package.
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
theorem inertia_fixed_primePower_of_potentiallyGood_fixed_point (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : q.Prime) (hqp : q ≠ p) (hj : ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ (n : ℕ) (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), p ^ n • y = 0 → τ • y = y := by sorry
end PrimeLocal
