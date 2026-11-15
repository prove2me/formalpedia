-- Prove2me | Theorems.Thm_PrimeLocal_exists_global_integral_model_minimal_at_all_primes
-- name    : PrimeLocal.exists_global_integral_model_minimal_at_all_primes
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:49:27.04789+00:00
-- url     : https://prove2.me/theorems/9fed868b-1b1d-4018-ace9-25e2c13a7c0d
-- title:
--   Global minimal integral model
-- statement:
--   Every elliptic curve over Q has an integral Weierstrass model that is minimal at every prime.
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
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

namespace PrimeLocal
theorem exists_global_integral_model_minimal_at_all_primes (E : WeierstrassCurve ℚ) [E.IsElliptic] : ∃ (W : WeierstrassCurve ℤ) (C : WeierstrassCurve.VariableChange ℚ), C • E = W.map (Int.castRingHom ℚ) ∧ W.Δ ≠ 0 ∧ ∀ (q : ℕ) [Fact q.Prime], WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q])) := by sorry
end PrimeLocal
