-- Prove2me | Theorems.Thm_WeierstrassCurve_galoisRep_supersingularShapeAt
-- name    : WeierstrassCurve.galoisRep_supersingularShapeAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/94f94032-aa7f-5f91-8906-608bf155a417
-- title:
--   Inertia at a good supersingular prime on E[p]
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and $p$ an odd prime. Assume: $p \nmid \Delta_W$ (the predicate `IsGoodPrimeFor`); $p$ divides the $i$-th coefficient of the polynomial $W.\mathrm{pre}\Psi' p$ for every $i$ with $1 \le i < (p^2-1)/2$; the group of $p$-torsion points, i.e. the $\mathbb{Z}$-torsion-by-$p$ submodule of the points of $W$ base-changed along $\mathbb{Z} \to \mathbb{Q}$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, has cardinality $p^2$; and $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$. Write $\bar\rho$ for `galoisRepModuleEnd`, the monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to the $\mathbb{Z}/p$-module endomorphisms of that $p$-torsion module induced by the Galois action, and $I_A$ for the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup. Then two things hold: first, there is a subgroup $W_d$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ containing every commutator $\sigma\tau\sigma^{-1}\tau^{-1}$ with $\sigma,\tau \in I_A$ and such that each $\sigma \in W_d$ has $\bar\rho(\sigma)^{p^n} = 1$ for some $n$; second, $p^2-1$ divides the cardinality of the image set $\bar\rho(I_A)$. Note that $W_d$ is not required to be contained in $I_A$.
--
--   This is the supersingular case of Serre's description of the shape of the inertia image on $E[p]$ at a prime of good reduction: tame inertia acts through a character of order divisible by $p^2-1$ valued in the non-split Cartan, modulo a normal subgroup on which the representation has $p$-power order. It is used in [`WeierstrassCurve.residualGaloisRepOf_restrict_index_two`](thm.html#WeierstrassCurve.residualGaloisRepOf_restrict_index_two) to verify the local hypothesis at $p$ needed for the restriction-of-index-two criterion, and it rests on the valuation computation for coordinates of $p$-torsion points in [`WeierstrassCurve.valuation_torsion_of_coeff_prePsi_dvd`](thm.html#WeierstrassCurve.valuation_torsion_of_coeff_prePsi_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_galoisRep_supersingularShapeAt.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.galoisRep_supersingularShapeAt (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    (∃ Wd : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ, σ * τ * σ⁻¹ * τ⁻¹ ∈ Wd) ∧
      (∀ σ ∈ Wd, ∃ n : ℕ,
        WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) p σ ^ p ^ n = 1)) ∧
    p ^ 2 - 1 ∣ Nat.card (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p ''
        (A.inertiaSubgroupIn ℚ : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) := by sorry
