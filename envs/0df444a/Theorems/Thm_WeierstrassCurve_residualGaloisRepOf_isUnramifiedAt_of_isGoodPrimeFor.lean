-- Prove2me | Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor
-- name    : WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/4f99b84f-f31d-5d6a-be48-1dadb3f4fa62
-- title:
--   Good reduction at q ≠ p: ρ̄_{E,p} is unramified at q
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb{Q}$ and let $W$ be a Weierstrass curve over $\mathbb{Z}$ which is an integral model of $E$, in the sense that some admissible change of variables over $\mathbb{Q}$ carries $E$ to the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$. Let $p$ be a prime, and assume that the $p$-torsion submodule of the group of points of $E$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` has cardinality $p^2$, and that the representation of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on this $\mathbb{Z}/p$-module by $\mathbb{Z}/p$-module endomorphisms factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $\sigma$ fixing $L$ pointwise acts as the identity. These two hypotheses make $E[p]$ a two-dimensional residual Galois representation $\bar\rho_{E,p}$ over $\mathbb{Z}/p$. Let $q$ be a prime with $q \neq p$ such that $q$ does not divide the discriminant $\Delta$ of $W$. Then $\bar\rho_{E,p}$ is unramified at $q$: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, every element of the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ acts as the identity on $E[p]$.
--
--   This is the easy direction of the criterion of Néron–Ogg–Shafarevich, stated for the mod-$p$ residual representation attached to an elliptic curve over $\mathbb{Q}$ with a prescribed integral Weierstrass model: away from $p$, primes not dividing the discriminant of the model are unramified for $\bar\rho_{E,p}$. It supplies the local condition at the good primes in the determination of the Serre level of $\bar\rho_{E,p}$, and is used in the construction of patching data for the modularity-lifting step and in the analysis of inertia at bad primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor (E : WeierstrassCurve ℚ) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E) (p : ℕ) [Fact p.Prime] (hcard : Nat.card (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) (hker : GaloisFactorsThroughFiniteLevel (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hgood : W.IsGoodPrimeFor q) : (E.residualGaloisRepOf p hcard hker).IsUnramifiedAt q := by sorry
