-- Prove2me | Theorems.Thm_ValuationSubring_henselianLocalRing_comap_of_forall_comap_eq_imp_eq
-- name    : ValuationSubring.henselianLocalRing_comap_of_forall_comap_eq_imp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/c2eefa6d-bc2e-56a6-9770-fbe080497835
-- title:
--   Unique extension to the algebraic closure implies henselian
-- statement:
--   Let $K$ be a field and let $\Omega$ be a field equipped with a $K$-algebra structure making it an algebraic closure of $K$ (algebraic over $K$ and algebraically closed). Let $A$ be a valuation subring of $\Omega$, assumed proper, i.e. $A \neq \Omega$. Write $A \cap K$ for the pullback `A.comap (algebraMap K Ω)`, the valuation subring of $K$ consisting of the elements of $K$ whose image in $\Omega$ lies in $A$. Assume that $A$ is the unique valuation subring of $\Omega$ with this pullback: for every valuation subring $B$ of $\Omega$, if $B \cap K = A \cap K$ as valuation subrings of $K$, then $B = A$. The conclusion is that the ring underlying $A \cap K$ is a henselian local ring, in the sense of Mathlib's `HenselianLocalRing`: it is local, and for every monic polynomial $f$ over it and every element $\bar a$ of its residue field with $f(\bar a) = 0$ and $f'(\bar a)$ a unit, there is a root $a$ of $f$ in the ring reducing to $\bar a$. No separability, rank or residue-characteristic restriction is imposed.
--
--   This is the implication "unique prolongation to the algebraic closure $\Rightarrow$ henselian" for valuation rings, valid in all characteristics and for valuations of arbitrary rank (Engler–Prestel, Neukirch). It is used in the construction of henselian valuation rings inside finite extensions, namely by [`ValuationSubring.exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional`](thm.html#ValuationSubring.exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_henselianLocalRing_comap_of_forall_comap_eq_imp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ValuationSubring.henselianLocalRing_comap_of_forall_comap_eq_imp_eq
    {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (hAtop : A ≠ ⊤)
    (huniq : ∀ B : ValuationSubring Ω,
      B.comap (algebraMap K Ω) = A.comap (algebraMap K Ω) → B = A) :
    HenselianLocalRing ↥(A.comap (algebraMap K Ω)) := by sorry
