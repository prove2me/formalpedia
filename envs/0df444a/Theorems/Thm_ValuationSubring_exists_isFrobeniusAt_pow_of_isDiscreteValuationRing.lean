-- Prove2me | Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_pow_of_isDiscreteValuationRing
-- name    : ValuationSubring.exists_isFrobeniusAt_pow_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b89cc506-a058-5375-9103-36bba17e5f3b
-- title:
--   Existence of a Frobenius element over a finite subextension
-- statement:
--   Let $R$ be a domain which is a discrete valuation ring whose residue field $\mathrm{ResidueField}\,R$ is finite, let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$, and let $\Omega$ be a field which is an algebraic closure of $K$ (as a $K$-algebra). Let $p$ be a natural number, prime by hypothesis, whose image in $R$ lies in the maximal ideal of $R$. Let $A$ be a valuation subring of $\Omega$ such that the image $\mathrm{algebraMap}\,K\,\Omega(\mathrm{algebraMap}\,R\,K(r))$ of every $r \in R$ lies in $A$, and assume $A \neq \top$, i.e. $A$ is not all of $\Omega$. Finally let $F$ be an intermediate field of $\Omega/K$ which is finite-dimensional over $K$. Then there exist a natural number $d$ and a $K$-algebra automorphism $\varphi$ of $\Omega$ such that $d > 0$, $\varphi z = z$ for every $z \in F$, and $\varphi$ is a Frobenius element at $A$ for the exponent $p^{d}$ in the sense of `IsFrobeniusAt`: namely $\varphi$ belongs to the decomposition subgroup of $A$ over $K$ (so that it acts on the residue field of $A$), and for every $x$ in the residue field of $A$ the element $\varphi$ of that subgroup sends $x$ to $x^{p^{d}}$.
--
--   This is the existence of a Frobenius element at a place of an algebraic closure of a local (or semi-local) field, in the relative form where the automorphism is required to fix a prescribed finite subextension $F/K$ pointwise, so that $p^d$ may be taken to be the size of the residue field of $A \cap F$. It feeds the refinement that separates tame from wild inertia, [`ValuationSubring.exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild_of_isDiscreteValuationRing`](thm.html#ValuationSubring.exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild_of_isDiscreteValuationRing), used in the study of Frobenius traces of elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_pow_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_isFrobeniusAt_pow_of_isDiscreteValuationRing
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (F : IntermediateField K Ω) [FiniteDimensional K ↥F] :
    ∃ (d : ℕ) (φ : Ω ≃ₐ[K] Ω), 0 < d ∧ (∀ z ∈ F, φ z = z) ∧ A.IsFrobeniusAt φ (p ^ d) := by sorry
