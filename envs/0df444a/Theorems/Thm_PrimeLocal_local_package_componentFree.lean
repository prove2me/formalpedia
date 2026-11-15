-- Prove2me | Theorems.Thm_PrimeLocal_local_package_componentFree
-- name    : PrimeLocal.local_package_componentFree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:58:27.051028+00:00
-- url     : https://prove2.me/theorems/be487f11-05cf-4f2e-a1a4-02a7e98465a5
-- title:
--   Local package for a rational point of prime order p >= 23
-- statement:
--   An elliptic curve over Q with a rational point of prime order p >= 23 has an integral model W minimal at all primes, with the transported point, satisfying multiplicative reduction at 2 and 3 with the point off the identity component there, the local clause at every q != p, and the clause at p, in the exact shape consumed by the cofixed-line theorems.
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
theorem local_package_componentFree (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (h23 : 23 ≤ p) (P : (E⁄ℚ).Point) (hP : addOrderOf P = p) : ∃ (W : WeierstrassCurve ℤ) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), W.Δ ≠ 0 ∧ (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) ∧ addOrderOf Q = p ∧ (2:ℤ) ∣ W.Δ ∧ ¬ (2:ℤ) ∣ W.c₄ ∧ (3:ℤ) ∣ W.Δ ∧ ¬ (3:ℤ) ∣ W.c₄ ∧ (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 → ¬ W.InZeroComponentAt A Q) ∧ (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 → ¬ W.InZeroComponentAt A Q) ∧ (∀ q : ℕ, q.Prime → q ≠ p →
      ¬ (q : ℤ) ∣ W.Δ ∨ ((q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄) ∨
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ τ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (n : ℕ) (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), p ^ n • y = 0 → τ • y = y) ∧ ((¬ (p : ℤ) ∣ W.Δ ∧ ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∃ (x y : AlgebraicClosure ℚ)
          (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
          p • (Point.some x y h) = 0 ∧ x ∈ A)
      ∨ ((p : ℤ) ∣ W.Δ ∧ ¬ (p : ℤ) ∣ W.c₄)) := by sorry
end PrimeLocal
