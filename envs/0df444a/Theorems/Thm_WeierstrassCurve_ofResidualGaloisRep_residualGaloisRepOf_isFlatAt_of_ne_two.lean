-- Prove2me | Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two
-- name    : WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/6dcbec0b-2ce2-56c0-a4f8-921eedf3e40a
-- title:
--   Flatness at odd p of the mod p representation of a good model
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a prime with $p \neq 2$, let $k$ be a finite field and let $\iota : \mathbb{Z}/p \to k$ be a ring homomorphism. Assume `W.IsGoodPrimeFor p`, i.e. $p \nmid \Delta_W$; assume that the $p$-torsion subgroup of the points of $W_{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$ has exactly $p^{2}$ elements; and assume that the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on that $p$-torsion, given by `galoisRepModuleEnd`, is trivial on the subgroup fixing some intermediate field $L$ with $L/\mathbb{Q}$ finite. These last two hypotheses produce the residual representation `residualGaloisRepOf` of the Galois group on the $p$-torsion, a two-dimensional $\mathbb{Z}/p$-representation. The conclusion is that its base change $k \otimes_{\mathbb{Z}/p} -$ along $\iota$, regarded as an object of [`GaloisRepAdic k`](def/GaloisRep_Adic.html#L16), satisfies `IsFlatAt p`: the residue field of $k$ is finite, and for every ideal $I \subseteq k$ with $k/I$ finite there exist a cocommutative Hopf algebra $H$ over the subring $\mathbb{Z}_{(p)} \subset \mathbb{Q}$ of rationals whose denominator is coprime to $p$, finite and flat as a $\mathbb{Z}_{(p)}$-module, and a bijection from the group of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ onto the quotient of the representation space by $I$ times it, which is additive and equivariant for the Galois action on homomorphisms and the induced action at level $I$.
--
--   This is the finite-flat (weight-two) local condition at $p$ for the mod $p$ representation attached to the $p$-torsion of an integral Weierstrass model with $p \nmid \Delta$, with coefficients extended to a finite field $k$: the $p$-torsion group scheme is prolonged to a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$. Only the case of odd $p$ is asserted, the statement for all primes being a separate, stronger assertion; it is used to verify the flatness part of the local deformation conditions, through [`WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two`](thm.html#WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {k : Type} [Field k] [Finite k]
    (ι : ZMod p →+* k) (hgood : W.IsGoodPrimeFor p)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p)) :
    (GaloisRepAdic.ofResidualGaloisRep
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι)).IsFlatAt p := by sorry
