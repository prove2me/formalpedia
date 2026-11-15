-- Prove2me | Theorems.Thm_PrimeLocal_dvd_discr_and_not_dvd_c4_iff_hasMultiplicativeReduction
-- name    : PrimeLocal.dvd_discr_and_not_dvd_c4_iff_hasMultiplicativeReduction
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:58:31.570911+00:00
-- url     : https://prove2.me/theorems/b8be59e7-cdb3-4972-824e-d381babb8dfe
-- title:
--   Multiplicative reduction criterion at a prime
-- statement:
--   For an integral Weierstrass model that is minimal at q, the reduction at q is multiplicative if and only if q divides the discriminant and does not divide c4.
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
theorem dvd_discr_and_not_dvd_c4_iff_hasMultiplicativeReduction (W : WeierstrassCurve ℤ) (q : ℕ) [Fact q.Prime] [WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))] :
    (W.map (Int.castRingHom ℚ_[q])).HasMultiplicativeReduction ℤ_[q] ↔
      (q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄ := by sorry
end PrimeLocal
