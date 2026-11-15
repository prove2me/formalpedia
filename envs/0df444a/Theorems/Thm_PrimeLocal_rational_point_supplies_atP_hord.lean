-- Prove2me | Theorems.Thm_PrimeLocal_rational_point_supplies_atP_hord
-- name    : PrimeLocal.rational_point_supplies_atP_hord
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:22:00.402206+00:00
-- url     : https://prove2.me/theorems/eca77e32-96e1-4339-8eb7-021755391e8c
-- title:
--   A rational p-torsion point supplies the good-at-p integrality witness
-- statement:
--   If the curve has good reduction at p >= 3 and a rational point of order p, then above p there is a p-torsion point with integral x-coordinate (the hord clause of the local package).
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
theorem rational_point_supplies_atP_hord (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → ∃ (x' y' : AlgebraicClosure ℚ) (h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x' y'), p • (Point.some x' y' h') = 0 ∧ x' ∈ A := by sorry
end PrimeLocal
