-- Prove2me | Theorems.Thm_ValuationSubring_exists_normal_commutator_mem_of_isDiscreteValuationRing
-- name    : ValuationSubring.exists_normal_commutator_mem_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/67e2c6c8-8037-5a5b-803b-52559c9093ab
-- title:
--   Uniformiser congruence subgroup of inertia is normal with abelian quotient
-- statement:
--   Let $K$ be a field and $L$ a field equipped with a $K$-algebra structure which is finite-dimensional over $K$ and Galois over $K$, and let $A$ be a valuation subring of $L$ whose underlying ring is a discrete valuation ring. Write $A.\mathrm{decompositionSubgroup}\ K$ for the decomposition group of $A$ in $\mathrm{Gal}(L/K)$ and $A.\mathrm{inertiaSubgroup}\ K$ for the inertia subgroup inside it, and let $\mathfrak m_A$ be the maximal ideal of the local ring $A$. The assertion is that there is a subgroup $P_w$ of the inertia group with the following three properties. First, $P_w$ is exactly the set of $\sigma$ in the inertia group such that for every irreducible element $\varpi$ of $A$ (equivalently, every uniformiser) one has $\sigma\cdot\varpi-\varpi\in\mathfrak m_A^{2}$, where $\sigma$ acts through its image in the decomposition group. Second, $P_w$ is normal in the inertia group. Third, every commutator $a^{-1}b^{-1}ab$ of elements $a,b$ of the inertia group lies in $P_w$; thus the quotient of the inertia group by $P_w$ is abelian. No hypothesis is imposed on the residue characteristic.
--
--   This is the classical first step of the filtration of the inertia group by higher ramification groups: $P_w$ is the kernel of the homomorphism $\theta_0$ sending $\sigma$ to the residue class of $\sigma(\varpi)/\varpi$ in the residue field, so that the wild part of inertia is cut out by a congruence modulo $\mathfrak m_A^2$ and the tame quotient is abelian. It is used by [`ValuationSubring.exists_normal_isPGroup_commutator_le_inertiaSubgroup`](thm.html#ValuationSubring.exists_normal_isPGroup_commutator_le_inertiaSubgroup), which combines it with the statement that this subgroup is a $p$-group in residue characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_normal_commutator_mem_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem ValuationSubring.exists_normal_commutator_mem_of_isDiscreteValuationRing
    (K : Type u) [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing ↥A] :
    ∃ Pw : Subgroup ↥(A.inertiaSubgroup K),
      (∀ σ : ↥(A.inertiaSubgroup K), σ ∈ Pw ↔
        ∀ ϖ : ↥A, Irreducible ϖ →
          ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) ∧
      Pw.Normal ∧ ∀ a b : ↥(A.inertiaSubgroup K), a⁻¹ * b⁻¹ * a * b ∈ Pw := by sorry
