-- Prove2me | Theorems.Thm_PrimeLocal_no_signed_point_of_multiplicative_at_p
-- name    : PrimeLocal.no_signed_point_of_multiplicative_at_p
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:13:00.506997+00:00
-- url     : https://prove2.me/theorems/51a3bb68-9bcd-4bb8-98bb-073c823a4711
-- title:
--   No signed torsion point at a multiplicative p
-- statement:
--   At a prime p of multiplicative reduction, no rational point of order p can carry the sign forced by the ramified twist.
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
theorem no_signed_point_of_multiplicative_at_p (W' : WeierstrassCurve ℤ) (hΔ : W'.Δ ≠ 0) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpΔ : (p : ℤ) ∣ W'.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W'.c₄) (Q' : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQ' : addOrderOf Q' = p) (s : AlgebraicClosure ℚ) (hs : s ^ 2 = (p : AlgebraicClosure ℚ)) (hsign : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (σ s = s → σ • Q' = Q') ∧ (σ s = -s → σ • Q' = -Q')) : False := by sorry
end PrimeLocal
