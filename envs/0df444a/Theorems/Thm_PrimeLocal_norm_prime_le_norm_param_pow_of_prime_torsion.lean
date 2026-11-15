-- Prove2me | Theorems.Thm_PrimeLocal_norm_prime_le_norm_param_pow_of_prime_torsion
-- name    : PrimeLocal.norm_prime_le_norm_param_pow_of_prime_torsion
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:21:59.77636+00:00
-- url     : https://prove2.me/theorems/e282fcd9-ad58-4b46-af74-bea28f67787e
-- title:
--   Norm bound for the parameter of a p-torsion point in the formal kernel
-- statement:
--   A nonzero p-torsion point in the formal kernel over the integers of C_p has parameter t = x/y with |p| <= |t|^(p-1).
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
theorem norm_prime_le_norm_param_pow_of_prime_torsion (p : ℕ) [Fact p.Prime] [DecidableEq ℂ_[p]] (D : WeierstrassCurve 𝓞_ℂ_[p]) (hΔ : D.Δ ≠ 0) (x y : ℂ_[p]) (h : (D.map (PadicComplexInt p).subtype).toAffine.Nonsingular x y) (hx : 1 < ‖x‖) (htor : p • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖(p : ℂ_[p])‖ ≤ ‖x / y‖ ^ (p - 1) := by sorry
end PrimeLocal
