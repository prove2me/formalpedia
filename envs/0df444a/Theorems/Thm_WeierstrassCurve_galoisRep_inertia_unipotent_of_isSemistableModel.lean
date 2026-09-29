-- Prove2me | Theorems.Thm_WeierstrassCurve_galoisRep_inertia_unipotent_of_isSemistableModel
-- name    : WeierstrassCurve.galoisRep_inertia_unipotent_of_isSemistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/f2a8d5e6-08c1-5121-b1ba-fa22405c2279
-- title:
--   Inertia at q ≠ p acts unipotently on p-torsion
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and $p$ a prime. Assume $\Delta_W \neq 0$; that $W$ is a semistable model, meaning that for every prime $\ell$ with $\ell \mid \Delta_W$ one has $\ell \nmid c_4(W)$; that the $\mathbb{Z}$-torsion submodule killed by $p$ of the group of points of the base change $W \otimes \mathbb{Q}$ over $\overline{\mathbb{Q}}$ (taken as `AlgebraicClosure ℚ`) has cardinality $p^2$; and that the representation `galoisRepModuleEnd`, sending $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to the $\mathbb{Z}/p$-linear endomorphism of that $p$-torsion module given by the Galois action, factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $L/\mathbb{Q}$ finite-dimensional such that every $\sigma$ fixing $L$ pointwise is sent to $1$. Let $q$ be a prime with $q \neq p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$, and let $\sigma$ lie in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ inside its decomposition subgroup. Then, writing $\rho(\sigma)$ for the endomorphism attached to $\sigma$, one has $(\rho(\sigma) - 1)(\rho(\sigma) - 1) = 0$.
--
--   This is the unipotence of inertia at primes away from $p$ on the mod $p$ representation of a semistable elliptic curve over $\mathbb{Q}$: at good primes inertia acts trivially, at multiplicative primes the Tate-curve filtration by the zero component gives a single unipotent jump. It is used in the analysis of the image of the residual representation, in particular for the index-two restriction statement and for the computation of the order of the inertia image.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_galoisRep_inertia_unipotent_of_isSemistableModel.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.galoisRep_inertia_unipotent_of_isSemistableModel (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p σ - 1) *
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p σ - 1) = 0 := by sorry
