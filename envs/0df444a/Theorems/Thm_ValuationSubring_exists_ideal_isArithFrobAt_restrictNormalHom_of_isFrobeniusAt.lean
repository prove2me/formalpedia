-- Prove2me | Theorems.Thm_ValuationSubring_exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt
-- name    : ValuationSubring.exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/c1c05978-850e-5c6d-a1e8-de3504000be7
-- title:
--   Frobenius at a place restricts to arithmetic Frobenius
-- statement:
--   Let $L$ be a field of characteristic zero (an algebra over $\mathbb{Q}$), and let $F$ be a number field which is an intermediate field, i.e. $F$ is a $\mathbb{Q}$-algebra and $L$ an $F$-algebra with the scalar towers compatible, and $F$ is normal over $\mathbb{Q}$. Let $A$ be a valuation subring of $L$, let $\ell$ be a prime number, and assume $A$ lies over $\ell$ in the sense that $(\ell : L)$ is a non-unit of $A$. Let $\tau$ be a $\mathbb{Q}$-algebra automorphism of $L$ which is a Frobenius at $A$ for $\ell$, that is: $\tau$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$, and the induced action of $\tau$ on the residue field of $A$ is $x \mapsto x^{\ell}$ for every $x$. Then there is an ideal $Q$ of the ring of integers $\mathcal{O}_F$ such that: an element $x \in \mathcal{O}_F$ lies in $Q$ precisely when its image in $L$ is a non-unit of $A$; $Q$ is maximal; $Q$ lies over the ideal $\ell\mathbb{Z} = \operatorname{span}\{(\ell : \mathbb{Z})\}$ of $\mathbb{Z}$; the quotient $\mathcal{O}_F / Q$ is finite; and the restriction $\tau|_F \in \operatorname{Gal}(F/\mathbb{Q})$, obtained through `AlgEquiv.restrictNormalHom`, is an arithmetic Frobenius at $Q$ relative to $\mathbb{Z}$, i.e. $\tau|_F(x) \equiv x^{\,\#(\mathbb{Z}/Q \cap \mathbb{Z})} \pmod{Q}$ for all $x \in \mathcal{O}_F$.
--
--   This is the dictionary between the two standard ways Frobenius elements enter the study of Galois representations: Frobenius elements at places of a large field, described through the decomposition group of a valuation subring and the $\ell$-power map on its residue field, and arithmetic Frobenius elements at maximal ideals of the ring of integers of a finite normal subfield, as used for Artin representations and their Hecke eigensystems. It is invoked in the Langlands–Tunnell part of the argument, in the construction of lifts attached to cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NumberField

theorem ValuationSubring.exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt
    {L : Type*} [Field L] [Algebra ℚ L]
    (F : Type*) [Field F] [Algebra ℚ F] [NumberField F] [Algebra F L] [IsScalarTower ℚ F L]
    [Normal ℚ F]
    (A : ValuationSubring L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ)
    {τ : L ≃ₐ[ℚ] L} (hτ : A.IsFrobeniusAt τ ℓ) :
    ∃ Q : Ideal (𝓞 F),
      (∀ x : 𝓞 F, x ∈ Q ↔ algebraMap F L (algebraMap (𝓞 F) F x) ∈ A.nonunits) ∧
      Q.IsMaximal ∧ Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ) ∧ Finite (𝓞 F ⧸ Q) ∧
      IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F τ) Q := by sorry
