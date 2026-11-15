-- Prove2me | Theorems.Thm_PrimeLocal_no_additive_integral_j_at_p
-- name    : PrimeLocal.no_additive_integral_j_at_p
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:53:57.764924+00:00
-- url     : https://prove2.me/theorems/2e92aec7-2a34-4093-bc1f-a2a10e125bf1
-- title:
--   No rational p-torsion with additive reduction and integral j at p
-- statement:
--   A curve minimal at p >= 23 with additive reduction and integral j at p has no rational point of order p (formal-kernel estimate after the degree-12 scaling).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal

namespace PrimeLocal
theorem no_additive_integral_j_at_p (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} [Fact p.Prime] (hmin : WeierstrassCurve.IsMinimal ℤ_[p] (W.map (Int.castRingHom ℚ_[p]))) (hp17 : 17 ≤ p) (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : (p : ℤ) ∣ W.c₄) (hj : ((p : ℤ) ^ padicValInt p W.Δ ∣ W.c₄ ^ 3)) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) : False := by sorry
end PrimeLocal
