-- Prove2me | Theorems.Thm_PrimeLocal_evalSeries_nthSeries_prime_ne_zero
-- name    : PrimeLocal.evalSeries_nthSeries_prime_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:22:10.345339+00:00
-- url     : https://prove2.me/theorems/ce751527-1818-45d3-a9ef-100c66d9cf02
-- title:
--   The p-series has no small nonzero zeros
-- statement:
--   For a commutative formal group over the integers of C_p and t with 0 < |t| < 1 and |t|^(p-1) < |p|, the evaluated p-series [p](t) is nonzero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_FormalGroup_NSeries

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal

namespace PrimeLocal
theorem evalSeries_nthSeries_prime_ne_zero (p : ℕ) [Fact p.Prime] (F : FormalGroup 𝓞_ℂ_[p]) [F.IsComm] (t : 𝓞_ℂ_[p]) (ht0 : t ≠ 0) (ht1 : ‖(t : ℂ_[p])‖ < 1) (hsmall : ‖(t : ℂ_[p])‖ ^ (p - 1) < ‖(p : ℂ_[p])‖) : FormalGroup.evalSeries (F.nthSeries p) t ≠ 0 := by sorry
end PrimeLocal
