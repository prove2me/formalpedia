-- Prove2me | Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt
-- name    : WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/96371cc9-4eac-5a9e-ba7d-a818d9956341
-- title:
--   Mod p representation unramified at good primes q ≠ p
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $p$ be a prime. Write $E = W.\mathrm{map}(\mathrm{Int.castRingHom}\ \mathbb{Q})$ for the Weierstrass curve over $\mathbb{Q}$ obtained by reducing the coefficients of $W$ along $\mathbb{Z} \to \mathbb{Q}$. Assume two hypotheses on the $p$-torsion of $E$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`: first, that the subgroup of points of $E$ over $\overline{\mathbb{Q}}$ killed by $p$ has cardinality exactly $p^2$; second, that the action homomorphism `galoisRepModuleEnd`, sending $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to the $\mathbb{Z}/p$-linear endomorphism of that $p$-torsion module given by the Galois action, factors through a finite level, i.e. there is an intermediate field $L$ with $\mathbb{Q} \subseteq L \subseteq \overline{\mathbb{Q}}$ finite-dimensional over $\mathbb{Q}$ such that every $\sigma$ fixing $L$ pointwise acts as the identity. Let $q$ be a prime with $q \neq p$ which is good for $W$ in the sense that $q$ does not divide the discriminant $W.\Delta$ in $\mathbb{Z}$. The conclusion is that the two-dimensional $\mathbb{Z}/p$-representation [`GaloisRepAdic.ofResidualGaloisRep (E.residualGaloisRepOf p hcard hker)`](def/GaloisRep_Adic.html#L196) — whose underlying module is the $p$-torsion of $E(\overline{\mathbb{Q}})$ with the Galois action above — is unramified at $q$: for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ over $\mathbb{Q}$, the endomorphism $\rho(\sigma)$ is the identity.
--
--   This is the Néron–Ogg–Shafarevich criterion in the shape needed downstream: good reduction at $q \nmid \Delta$ forces inertia at $q$ to act trivially on $p$-torsion for $q \neq p$. It is the local-at-$q$ input for [`WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two`](thm.html#WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two) and [`WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_ordinaryCondition`](thm.html#WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_ordinaryCondition), and asserts nothing about deformation rings or modularity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hgood : W.IsGoodPrimeFor q) :
    (GaloisRepAdic.ofResidualGaloisRep
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).IsUnramifiedAt q := by sorry
