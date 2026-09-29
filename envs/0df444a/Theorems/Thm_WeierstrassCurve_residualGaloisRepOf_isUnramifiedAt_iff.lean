-- Prove2me | Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff
-- name    : WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/b9baa4e4-89ec-501b-abe7-1055ee29fa48
-- title:
--   Unramifiedness of packaged mod-p representation as pointwise inertia-triviality
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Q}$ and $p$ a prime. Assume that the $\mathbb{Z}$-torsion submodule killed by $p$ of the group of points of $W$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ has exactly $p^2$ elements, and that the Galois action on this submodule, viewed as the monoid homomorphism `galoisRepModuleEnd` from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{End}_{\mathbb{Z}/p}$ of that submodule induced by the scalar action, satisfies [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17): there is a finite-dimensional intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ such that every automorphism fixing $L$ pointwise is sent to $1$. Let $q$ be a natural number. Then the packaged residual representation `W.residualGaloisRepOf p hcard hker` — whose underlying $\mathbb{Z}/p$-vector space is that $p$-torsion submodule, of rank $2$ by the cardinality hypothesis, with $\rho$ the above homomorphism — is unramified at $q$, i.e. for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q \in A.\mathrm{nonunits}$ and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$, the endomorphism $\rho(\sigma)$ is the identity, if and only if for every such $A$ and $\sigma$ and every point $x$ of that $p$-torsion submodule one has $\sigma \bullet x = x$.
--
--   This identifies the representation-level unramifiedness predicate of the packaged two-dimensional mod-$p$ representation attached to a Weierstrass curve over $\mathbb{Q}$ with the curve-level predicate asserting that inertia at $q$ fixes each $p$-torsion point. It serves as the translation between the two vocabularies, and is used in the level-lowering step for Frey packages at odd primes and in the statements about residual modularity of prescribed level and about good primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_iff (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p))
    (q : ℕ) :
    (W.residualGaloisRepOf p hcard hker).IsUnramifiedAt q ↔
      WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ W p q := by sorry
