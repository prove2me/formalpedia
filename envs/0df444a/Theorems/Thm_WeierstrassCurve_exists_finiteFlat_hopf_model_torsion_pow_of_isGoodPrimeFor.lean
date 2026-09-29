-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor
-- name    : WeierstrassCurve.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/6f695f8b-ff54-5434-84c4-afa56a82624b
-- title:
--   Finite flat Hopf model of pⁿ-torsion at odd good primes
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $p$ be a prime with $p \neq 2$ such that $p$, viewed in $\mathbb{Z}$, does not divide the discriminant $\Delta$ of $W$ (this is the content of `W.IsGoodPrimeFor p`). Write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Then for every $n > 0$ there exist a type $H$, a commutative ring structure on $H$ and a Hopf-algebra structure on $H$ over $R$ such that $H$ is finite and flat as an $R$-module and cocommutative as an $R$-coalgebra, together with a bijection $e$ from `WithConv (H →ₐ[R] AlgebraicClosure ℚ)`, the set of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ equipped with its convolution monoid structure, onto the $\mathbb{Z}$-submodule `Submodule.torsionBy ℤ … ((p ^ n : ℕ) : ℤ)` of elements killed by $p^n$ in the group of points of the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$ over $\overline{\mathbb{Q}}$, subject to two compatibilities: $e(f g) = e(f) + e(g)$ for all $f, g$, so $e$ turns convolution into addition of points; and, for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all $f, g$, if $g(h) = \sigma(f(h))$ for every $h \in H$ then $e(g) = \sigma \bullet e(f)$, the action being the coordinatewise Galois action on points. No uniqueness of $H$ is asserted, and nothing is claimed for $p = 2$ or for $n = 0$.
--
--   This is the statement that, at an odd prime of good reduction, the $p^n$-torsion of the elliptic curve is the generic fibre of a finite flat commutative group scheme over the local ring $\mathbb{Z}_{(p)}$, presented on the dual side as a finite flat cocommutative Hopf algebra whose $\overline{\mathbb{Q}}$-points, with convolution, are Galois-equivariantly identified with $E[p^n](\overline{\mathbb{Q}})$. It feeds the flatness hypotheses imposed on the residual representation and on the Tate module representation in the modularity-lifting input, being cited by [`WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two`](thm.html#WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two) and by the two `tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd` statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hgood : W.IsGoodPrimeFor p) (hp2 : p ≠ 2) :
    ∀ n : ℕ, 0 < n →
      ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
        Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
        ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
            Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ),
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry
