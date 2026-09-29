-- Prove2me | Theorems.Thm_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal
-- name    : ValuationSubring.exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b64698dc-e52f-5a36-9553-f71d2723c17f
-- title:
--   Weierstrass preparation over a henselian valuation ring
-- statement:
--   Let $L$ be an algebraically closed field and let $A \subseteq L$ be a valuation subring whose underlying local ring is henselian. Let $S$ be a commutative local ring equipped with an $A$-algebra structure whose structure map $A \to S$ is a local homomorphism, and assume $S$ is essentially of finite type over $A$. Suppose further: the composite $A \to S \to S/\mathfrak m_S$ onto the residue field of $S$ is surjective; there is an element $t \in S$ with $\mathfrak m_S = (t) + \mathfrak m_A S$, where $\mathfrak m_A S$ denotes the image ideal of the maximal ideal $\mathfrak m_A$ of $A$ under $A \to S$; and $\mathfrak m_A S$ is a prime ideal of $S$. Then for every $h \in S$ not lying in $\mathfrak m_A S$ there exist a natural number $n$, a unit $u \in S^\times$ and a family $r \colon \mathrm{Fin}\,n \to A$ with every $r_i \in \mathfrak m_A$, such that $$h = u \prod_{i} \bigl(t - r_i\bigr)$$ in $S$, the $r_i$ being read in $S$ via the structure map.
--
--   This is the Weierstrass preparation theorem in the local ring of a smooth point of a relative curve over a henselian valuation ring, with $t$ playing the role of an étale coordinate: up to a unit, an element with nonzero image in the fibre $S/\mathfrak m_A S$ is a monic polynomial in $t$ whose roots all lie in the maximal ideal of $A$. It is used in the construction of smooth-point data for proper algebraic curves, via [`AlgebraicCurve.exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper`](thm.html#AlgebraicCurve.exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

universe u

theorem ValuationSubring.exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L) [HenselianLocalRing ↥A]
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra ↥A S] [IsLocalHom (algebraMap ↥A S)]
    [Algebra.EssFiniteType ↥A S]
    (hres : Function.Surjective (algebraMap ↥A (ResidueField S)))
    (t : S) (ht : maximalIdeal S = Ideal.span {t} ⊔ (maximalIdeal ↥A).map (algebraMap ↥A S))
    (hprime : ((maximalIdeal ↥A).map (algebraMap ↥A S)).IsPrime)
    (h : S) (hh : h ∉ (maximalIdeal ↥A).map (algebraMap ↥A S)) :
    ∃ (n : ℕ) (u : Sˣ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) ∧
      h = (u : S) * ∏ i, (t - algebraMap ↥A S (r i)) := by sorry
