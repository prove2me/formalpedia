-- Prove2me | Theorems.Thm_PrimeLocal_transport_rational_point_to_integral_model
-- name    : PrimeLocal.transport_rational_point_to_integral_model
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:49:24.483667+00:00
-- url     : https://prove2.me/theorems/d673b013-428a-47a6-8280-6b1a87f2874b
-- title:
--   Transport of a rational torsion point to an integral model
-- statement:
--   A rational point of given order on E transports, along the change of variables to an integral model, to a rational point of the same order with the same Galois fixedness.
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
theorem transport_rational_point_to_integral_model (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ) (C : WeierstrassCurve.VariableChange ℚ) (hC : C • E = W.map (Int.castRingHom ℚ)) (hΔ : W.Δ ≠ 0) {p : ℕ} (P : (E⁄ℚ).Point) (hP : addOrderOf P = p) (hp : p.Prime) : ∃ (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular (algebraMap ℚ (AlgebraicClosure ℚ) x) (algebraMap ℚ (AlgebraicClosure ℚ) y)), addOrderOf (Point.some x y h) = p ∧ addOrderOf (Point.some _ _ h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = p ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • (Point.some _ _ h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = Point.some _ _ h' := by sorry
end PrimeLocal
