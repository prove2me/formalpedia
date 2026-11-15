-- Prove2me | Theorems.Thm_PrimeLocal_multiplicative_at_two_or_three
-- name    : PrimeLocal.multiplicative_at_two_or_three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:29:10.056659+00:00
-- url     : https://prove2.me/theorems/ccfaa161-0d81-4095-a369-334542b22a21
-- title:
--   Multiplicative reduction at 2 and 3 for a rational point of large prime order
-- statement:
--   If an integral model minimal at q in {2, 3} has a rational point of prime order p >= 23 (with the fixedness hypotheses of the local package), then the reduction at q is multiplicative: q divides the discriminant and not c4.
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
theorem multiplicative_at_two_or_three (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} [Fact q.Prime] (hq23 : q = 2 ∨ q = 3) (hmin : WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))) (hp : p.Prime) (hp23 : 23 ≤ p) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : (q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄ := by sorry
end PrimeLocal
