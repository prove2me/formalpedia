-- Prove2me | Theorems.Thm_ValuationSubring_exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq
-- name    : ValuationSubring.exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/d114b092-88e2-53ab-aee1-abb2df83821f
-- title:
--   Elements fixed by the decomposition group have values from K
-- statement:
--   Let $C$ be a discrete valuation ring (a commutative domain which is a discrete valuation ring), let $K$ be a field that is a $C$-algebra and a fraction field of $C$, and let $M$ be a field which is a $K$-algebra and a $C$-algebra compatibly (scalar tower), finite-dimensional over $K$ and Galois over $K$. Let $V$ be a valuation subring of $M$ such that, first, $\mathrm{algebraMap}\,C\,M\,c \in V$ for every $c \in C$, and second, for every $c \in C$ the element $\mathrm{algebraMap}\,C\,M\,c$ lies in `V.nonunits` (the non-units of $V$, i.e. its maximal ideal) precisely when $c$ lies in the maximal ideal of $C$; thus $V$ is a valuation ring of $M$ lying over $C$ and inducing its valuation. Let $z \in M$ be nonzero and suppose $\sigma z = z$ for every $K$-algebra automorphism $\sigma$ of $M$ whose (pointwise) action satisfies $\sigma \bullet V = V$, i.e. $z$ is fixed by the decomposition group of $V$. The conclusion is that there exists $c \in K$ with $c \neq 0$ such that both $z \cdot (\mathrm{algebraMap}\,K\,M\,c)^{-1} \in V$ and $(\mathrm{algebraMap}\,K\,M\,c) \cdot z^{-1} \in V$; that is, $z$ and the image of $c$ have the same value for the valuation attached to $V$.
--
--   This is the finite-level statement that the extension of valued fields from $K$ to the decomposition field of a prolongation $V$ is immediate in value group: an element fixed by the stabiliser of $V$ in $\mathrm{Gal}(M/K)$ has the same value as some element of $K$. It is proved by passing from $V$ to a maximal ideal of the integral closure of $C$ in $M$, using that the ramification index and residue degree of the corresponding prime of the decomposition field over $C$ are both $1$, and it is used in the proof that the pullback of $V$ along such a fixed subfield is again a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped Pointwise

theorem ValuationSubring.exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type u) [Field K] [Algebra C K] [IsFractionRing C K]
    {M : Type u} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
    [FiniteDimensional K M] [IsGalois K M]
    (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C)
    (z : M) (hz : z ≠ 0)
    (hfix : ∀ σ : M ≃ₐ[K] M, σ • V = V → σ z = z) :
    ∃ c : K, c ≠ 0 ∧ z * (algebraMap K M c)⁻¹ ∈ V ∧ algebraMap K M c * z⁻¹ ∈ V := by sorry
