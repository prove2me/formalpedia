-- Prove2me | Theorems.Thm_ValuationSubring_natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime
-- name    : ValuationSubring.natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/cdff648e-5503-5aa1-9f31-2de9edc7d3d3
-- title:
--   Integral points as Galois-fixed points in a valuation ring
-- statement:
--   Let $p$ be a natural number and let $A$ be a valuation subring of $\overline{\mathbf Q} =$ `AlgebraicClosure ℚ` such that the image of $p$ in $\overline{\mathbf Q}$ lies in the set of non-units of $A$ (this is the meaning of `A.LiesOverPrime p`). Let $K$ be a commutative ring equipped with a $\mathbf Z$-algebra structure, and assume that for every prime number $\ell \neq p$ the tensor product $\mathbf Z_{(\ell)} \otimes_{\mathbf Z} K$ is a finite module over $\mathbf Z_{(\ell)}$, where $\mathbf Z_{(\ell)}$ is realised as [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8), the subring of those rationals whose denominator is coprime to $\ell$. Then the number of $\mathbf Z$-algebra homomorphisms $K \to \mathbf Z$ equals the number of those $\mathbf Z$-algebra homomorphisms $\varphi : K \to A$ whose image is pointwise fixed by every ring automorphism of $\overline{\mathbf Q}$, i.e. with $\sigma(\varphi(x)) = \varphi(x)$ in $\overline{\mathbf Q}$ for all ring automorphisms $\sigma$ of $\overline{\mathbf Q}$ and all $x \in K$. Both sides are cardinalities in the sense of `Nat.card`, so each is $0$ if the corresponding set is infinite. No primality hypothesis on $p$ is imposed.
--
--   This is the counting lemma, in the style of Mazur's discussion of integral points on affine schemes over $\mathbf Z$, identifying $\mathbf Z$-points of $\operatorname{Spec} K$ with the Galois-invariant $A$-points when $K$ is finite over $\mathbf Z$ away from $p$. It is used in the analysis of primary torsion in the Néron model of $J_0$, where the $\mathbf Z$-points of a finite flat group scheme are compared with points valued in a valuation ring above $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime
    (p : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : Type) [CommRing K] [Algebra ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ)
        (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K)) :
    Nat.card (K →ₐ[ℤ] ℤ)
      = Nat.card {φ : K →ₐ[ℤ] ↥A //
          ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (x : K),
            σ (φ x : AlgebraicClosure ℚ) = (φ x : AlgebraicClosure ℚ)} := by sorry
