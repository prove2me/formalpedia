-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt
-- name    : WeierstrassCurve.exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/a3361bf0-0c29-5e72-8099-7cdb2f734e09
-- title:
--   Frobenius-equivariant isomorphism of p-torsion under reduction at ℓ
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$ and let $\ell$ and $p$ be distinct primes such that $\ell$ is a good prime for $W$ in the sense that $(\ell : \mathbb Z)$ does not divide the discriminant $W.\Delta$. Let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $\ell$, meaning that the image of $\ell$ in $\overline{\mathbb Q}$ is a non-unit of $A$, and write $k_A$ for the residue field `IsLocalRing.ResidueField A`. Let $\sigma$ be a $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ which is a Frobenius element at $A$ for $\ell$, i.e. $\sigma$ belongs to the decomposition subgroup of $A$ over $\mathbb Q$ and the induced action of $\sigma$ on $k_A$ is $x \mapsto x^{\ell}$; and let $\varphi$ be a $\mathbb Z$-algebra automorphism of $k_A$ with $\varphi(x) = x^{\ell}$ for all $x \in k_A$. Then there exists a $\mathbb Z/p$-linear isomorphism $e$ from the $p$-torsion submodule (the $\mathbb Z$-torsion by $p$) of the group of points of $W$ base changed to $\overline{\mathbb Q}$ onto the $p$-torsion submodule of the group of points of $W$ base changed to $k_A$, such that $e(\sigma \cdot x) = \varphi \cdot e(x)$ for every $p$-torsion point $x$ over $\overline{\mathbb Q}$, the two actions being those of $\sigma$ and of $\varphi$ on points induced by the respective field automorphisms. The isomorphism is only asserted to exist; it is not required to be the reduction map.
--
--   This is the transport of the mod $p$ Galois representation of an elliptic curve with good reduction at $\ell$ to the $p$-torsion of the reduced curve over the algebraically closed residue field, the statement that reduction is a Frobenius-equivariant isomorphism on torsion prime to the residue characteristic. It is used to compute the determinant and the trace of the mod $p$ representation at a Frobenius element, in [`WeierstrassCurve.det_galoisRep_frobenius_eq_prime`](thm.html#WeierstrassCurve.det_galoisRep_frobenius_eq_prime) and [`WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel`](thm.html#WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt.lean

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped Classical

theorem WeierstrassCurve.exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt (W : WeierstrassCurve ℤ) (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) (φ : IsLocalRing.ResidueField A ≃ₐ[ℤ] IsLocalRing.ResidueField A) (hφ : ∀ x : IsLocalRing.ResidueField A, φ x = x ^ ℓ) : ∃ e : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p ≃ₗ[ZMod p] Submodule.torsionBy ℤ (W⁄(IsLocalRing.ResidueField A)).Point p, ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p, e (σ • x) = φ • e x := by sorry
