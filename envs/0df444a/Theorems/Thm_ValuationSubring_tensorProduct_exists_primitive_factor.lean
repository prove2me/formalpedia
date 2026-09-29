-- Prove2me | Theorems.Thm_ValuationSubring_tensorProduct_exists_primitive_factor
-- name    : ValuationSubring.tensorProduct_exists_primitive_factor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/148b7078-e402-5845-8e30-a27e63cdcad1
-- title:
--   Primitive factors in F ⊗_K A over a valuation subring
-- statement:
--   Let $K$ be a field, let $F$ be a nontrivial commutative ring without zero divisors which is a $K$-algebra, and let $K'$ be a field which is a $K$-algebra. Let $A$ be a valuation subring of $K'$, assume that $\mathrm{algebraMap}\ K\ K'$ takes every $c \in K$ into $A$ (hypothesis `hK`), and let $\sigma : A \to K$ be a ring homomorphism whose kernel is the maximal ideal of the local ring $A$, and which is a section of $K \to A$ in the sense that $\sigma$ applied to the element of $A$ determined by $c \in K$ equals $c$. Equipping $A$ with the $K$-algebra structure given by the corestriction of $\mathrm{algebraMap}\ K\ K'$ to $A$, let $\mathrm{h\sigma Alg} : A \to F$ be the $K$-algebra map $\sigma$ followed by $\mathrm{algebraMap}\ K\ F$, and let $\Psi : F \otimes_K A \to F$ be the $K$-algebra homomorphism obtained from the identity of $F$ and $\mathrm{h\sigma Alg}$ (their images commute since $F$ is commutative), i.e. $\Psi(f \otimes a) = f \cdot \sigma(a)$. The assertion is that every nonzero $z \in F \otimes_K A$ can be written as $z = (1 \otimes a) \cdot z'$ with $a \in A$ nonzero and $z' \in F \otimes_K A$ satisfying $\Psi(z') \neq 0$.
--
--   This is the Gauss content lemma for the tensor product $F \otimes_K A$ over a valuation subring: a nonzero element factors as a content $a \in A$ times an element of unit content, which therefore survives the reduction $\Psi$ induced by the $K$-rational residue map $\sigma$. It is used in the construction of a regular prolongation together with its retraction for a valuation subring of a function field whose constant field is $K$, in [`AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring`](thm.html#AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_tensorProduct_exists_primitive_factor.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing TensorProduct

theorem ValuationSubring.tensorProduct_exists_primitive_factor
    (K F K' : Type*) [Field K] [CommRing F] [Nontrivial F] [NoZeroDivisors F]
    [Field K'] [Algebra K F] [Algebra K K']
    (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K)
    (hker : RingHom.ker σ = maximalIdeal A)
    (hsec : ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c) :
    letI : Algebra K A := ((algebraMap K K').codRestrict A.toSubring hK).toAlgebra
    let hσAlg : A →ₐ[K] F :=
      { toRingHom := (algebraMap K F).comp σ
        commutes' := fun c ↦ congrArg (algebraMap K F) (hsec c) }
    let Ψ : TensorProduct K F A →ₐ[K] F :=
      Algebra.TensorProduct.lift (AlgHom.id K F) hσAlg (fun f a ↦ mul_comm _ _)
    ∀ z : TensorProduct K F A, z ≠ 0 →
      ∃ a : A, a ≠ 0 ∧ ∃ z' : TensorProduct K F A,
        z = ((1 : F) ⊗ₜ[K] a) * z' ∧ Ψ z' ≠ 0 := by sorry
