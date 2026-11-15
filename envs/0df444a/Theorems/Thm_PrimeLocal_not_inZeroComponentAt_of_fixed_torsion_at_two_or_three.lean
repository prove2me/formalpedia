-- Prove2me | Theorems.Thm_PrimeLocal_not_inZeroComponentAt_of_fixed_torsion_at_two_or_three
-- name    : PrimeLocal.not_inZeroComponentAt_of_fixed_torsion_at_two_or_three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:29:12.453792+00:00
-- url     : https://prove2.me/theorems/688f1fe6-7c9f-4662-89ce-6ee4c1ae1848
-- title:
--   A rational point of large prime order lies off the identity component at 2 and 3
-- statement:
--   Under the same hypotheses, the rational point of order p does not lie in the identity component of the Neron model at any prime above 2 or 3.
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
theorem not_inZeroComponentAt_of_fixed_torsion_at_two_or_three (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} (hq : q.Prime) (hq23 : q = 2 ∨ q = 3) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hp : p.Prime) (hp7 : 7 ≤ p) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ¬ W.InZeroComponentAt A Q := by sorry
end PrimeLocal
