-- Prove2me | Theorems.Thm_WeierstrassCurve_card_range_galoisRep_three_le_two
-- name    : WeierstrassCurve.card_range_galoisRep_three_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/2a01ac14-ee6e-5156-98b5-b33756c145d2
-- title:
--   Mod 3 image of order at most two
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$ with $\Delta_W \neq 0$, and let $W_{\mathbb Q}$ be its base change along $\mathbb Z \to \mathbb Q$. Consider the $3$-torsion submodule of the group of points of $W_{\mathbb Q}$ over $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, together with the natural homomorphism $\bar\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to the $\mathbb Z/3$-linear endomorphisms of that torsion module induced by the Galois action (`galoisRepModuleEnd`, the map coming from the distributive action). Assume: (i) the $3$-torsion has exactly $3^2$ elements; (ii) for every prime $q \neq 3$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, every element of the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$ is sent by $\bar\rho$ to the identity endomorphism; (iii) for every valuation subring $A$ of $\overline{\mathbb Q}$ with $3$ a non-unit of $A$, the $\bar\rho$-image of that inertia subgroup has at most $2$ elements. Then the range of $\bar\rho$ has at most $2$ elements.
--
--   This is the $p = 3$ local-to-global input in Wiles' argument: a mod $3$ representation attached to an elliptic curve over $\mathbb Q$ which is unramified outside $3$ and has inertia image of order at most $2$ at $3$ has global image of order at most $2$, the point being that the field cut out is totally complex (it contains the cube roots of unity, by [`WeierstrassCurve.apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one`](thm.html#WeierstrassCurve.apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one)), unramified outside $3$ and tamely ramified of index at most $2$ above $3$, whence of degree at most $2$ over $\mathbb Q$ by a Minkowski-type discriminant bound. It is used by [`WeierstrassCurve.residualGaloisRepOf_restrict_index_two`](thm.html#WeierstrassCurve.residualGaloisRepOf_restrict_index_two) to verify the hypothesis at $3$ on the residual representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_card_range_galoisRep_three_le_two.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.card_range_galoisRep_three_le_two (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point 3) = 3 ^ 2)
    (hunr : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) 3 σ = 1)
    (hle2 : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
      Nat.card (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) 3 ''
          (A.inertiaSubgroupIn ℚ : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) ≤ 2) :
    Nat.card (Set.range (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) 3)) ≤ 2 := by sorry
