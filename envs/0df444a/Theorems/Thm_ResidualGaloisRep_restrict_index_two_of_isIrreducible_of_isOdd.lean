-- Prove2me | Theorems.Thm_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd
-- name    : ResidualGaloisRep.restrict_index_two_of_isIrreducible_of_isOdd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/d3ea5c55-1c9e-5851-806b-9828d0657c47
-- title:
--   Index-two restrictions of an odd irreducible residual representation
-- statement:
--   Let $p$ be a prime with $p \neq 2$ and let $\rho$ be a residual Galois representation over $\mathbb{Z}/p$: a two-dimensional $\mathbb{Z}/p$-vector space $\rho.V$ together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_{\mathbb{Z}/p}(\rho.V)$ which is trivial on the subgroup fixing some finite-dimensional intermediate field. Assume: (hirr) every submodule of $\rho.V$ stable under all $\rho.\rho\,\sigma$ is $\bot$ or $\top$; (hodd) $\det \rho.\rho\,c = -1$ for every involution $c \neq 1$; (hnoext) every open subgroup $H$ containing `A.inertiaSubgroupIn ℚ` for every prime $q$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$ equals $\top$; (hq) for $q \neq p$ and such $A$, $(\rho.\rho\,\sigma - 1)^2 = 0$ on inertia; (hcyc) for $A$ over $p$, every $a \in (\mathbb{Z}/p)^\times$ is $\det \rho.\rho\,\sigma$ for some inertial $\sigma$; (hp_local) for every $A$ over $p$, either there is a proper submodule $L$ with $\rho.\rho\,\sigma\,v - v \in L$ for all inertial $\sigma$ and all $v$, or the commutators of inertia lie in a subgroup on which $\rho.\rho$ takes values of $p$-power order and $p^2 - 1$ divides the cardinality of the image of inertia; (h3) when $p = 3$, triviality of $\rho.\rho$ on inertia at all $q \neq 3$ together with inertia image of cardinality $\leq 2$ at $3$ forces the image of $\rho.\rho$ to have cardinality $\leq 2$. Then for every field $K$ that is a $\mathbb{Z}/p$-algebra, every index-two subgroup $H_0$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every $K$-submodule $\ell$ of $K \otimes_{\mathbb{Z}/p} \rho.V$ stable under the base-changed operators $\rho.\rho\,\sigma$ for $\sigma \in H_0$, one has $\ell = \bot$ or $\ell = \top$.
--
--   This is the abstract form of the assertion that such a residual representation stays absolutely irreducible after restriction to any index-two subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, the hypotheses encoding irreducibility, oddness and the semistable local behaviour at $p$ and away from $p$. It is invoked by [`WeierstrassCurve.residualGaloisRepOf_restrict_index_two`](thm.html#WeierstrassCurve.residualGaloisRepOf_restrict_index_two), where the local hypotheses are verified for the $p$-torsion representation of a semistable elliptic curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_restrict_index_two_of_isIrreducible_of_isOdd.lean

import Mathlib.FieldTheory.KrullTopology
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ResidualGaloisRep.restrict_index_two_of_isIrreducible_of_isOdd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ρ : ResidualGaloisRep (ZMod p))
    (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd)
    (hnoext : ∀ H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      (∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        A.inertiaSubgroupIn ℚ ≤ H) → H = ⊤)
    (hq : ∀ q : ℕ, q.Prime → q ≠ p → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, (ρ.ρ σ - 1) * (ρ.ρ σ - 1) = 0)
    (hcyc : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∀ a : (ZMod p)ˣ, ∃ σ ∈ A.inertiaSubgroupIn ℚ, LinearMap.det (ρ.ρ σ) = a)
    (hp_local :
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∃ L : Submodule (ZMod p) ρ.V, L ≠ ⊤ ∧
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) ∨
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (∃ W : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ, σ * τ * σ⁻¹ * τ⁻¹ ∈ W) ∧
          (∀ σ ∈ W, ∃ n : ℕ, ρ.ρ σ ^ p ^ n = 1)) ∧
        p ^ 2 - 1 ∣ Nat.card (ρ.ρ '' (A.inertiaSubgroupIn ℚ :
          Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))))
    (h3 : p = 3 →
      (∀ q : ℕ, q.Prime → q ≠ p → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ.ρ σ = 1) →
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        Nat.card (ρ.ρ '' (A.inertiaSubgroupIn ℚ :
          Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) ≤ 2) →
      Nat.card (Set.range ρ.ρ) ≤ 2)
    (K : Type) [Field K] [Algebra (ZMod p) K]
    (H₀ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hH₀ : H₀.index = 2)
    (ℓ : Submodule K (ρ.baseChange K).V)
    (hℓ : ∀ σ ∈ H₀, ∀ x ∈ ℓ, (ρ.baseChange K).ρ σ x ∈ ℓ) :
    ℓ = ⊥ ∨ ℓ = ⊤ := by sorry
