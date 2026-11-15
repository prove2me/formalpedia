-- Prove2me | Theorems.Thm_PrimeLocal_not_dvd_discr_iff_hasGoodReduction
-- name    : PrimeLocal.not_dvd_discr_iff_hasGoodReduction
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:58:29.611205+00:00
-- url     : https://prove2.me/theorems/a8fa735e-c7c8-4be6-8ec6-7ffde5afaa74
-- title:
--   Good reduction criterion at a prime
-- statement:
--   For an integral Weierstrass model that is minimal at q, the reduction at q is good if and only if q does not divide the discriminant.
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
theorem not_dvd_discr_iff_hasGoodReduction (W : WeierstrassCurve ℤ) (q : ℕ) [Fact q.Prime] [WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))] :
    (W.map (Int.castRingHom ℚ_[q])).HasGoodReduction ℤ_[q] ↔ ¬ (q : ℤ) ∣ W.Δ := by sorry
end PrimeLocal
