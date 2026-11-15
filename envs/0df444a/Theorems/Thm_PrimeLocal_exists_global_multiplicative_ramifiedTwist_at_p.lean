-- Prove2me | Theorems.Thm_PrimeLocal_exists_global_multiplicative_ramifiedTwist_at_p
-- name    : PrimeLocal.exists_global_multiplicative_ramifiedTwist_at_p
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:13:00.75157+00:00
-- url     : https://prove2.me/theorems/0b3eebc5-fbc6-477b-b9ba-5340d7c3775e
-- title:
--   Ramified quadratic twist at a multiplicative prime p
-- statement:
--   At a prime p of multiplicative reduction, a suitable ramified quadratic twist gives a global model with the sign behaviour needed for the at-p argument.
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
open IsLocalRing IsDedekindDomain.HeightOneSpectrum
open scoped WeierstrassCurve.Affine NNReal

namespace PrimeLocal
theorem exists_global_multiplicative_ramifiedTwist_at_p (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} [Fact p.Prime] (hmin : WeierstrassCurve.IsMinimal ℤ_[p] (W.map (Int.castRingHom ℚ_[p]))) (hp5 : 5 ≤ p) (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : (p : ℤ) ∣ W.c₄) (hj : ¬ ((p : ℤ) ^ padicValInt p W.Δ ∣ W.c₄ ^ 3)) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : ∃ (W' : WeierstrassCurve ℤ) (Q' : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (s : AlgebraicClosure ℚ), s ^ 2 = (p : AlgebraicClosure ℚ) ∧ W'.Δ ≠ 0 ∧ (p : ℤ) ∣ W'.Δ ∧ ¬ (p : ℤ) ∣ W'.c₄ ∧ addOrderOf Q' = p ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (σ s = s → σ • Q' = Q') ∧ (σ s = -s → σ • Q' = -Q') := by sorry
end PrimeLocal
