-- Prove2me | Theorems.Thm_ValuationSubring_exists_normal_isPGroup_commutator_le_inertiaSubgroup
-- name    : ValuationSubring.exists_normal_isPGroup_commutator_le_inertiaSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/e38a99e6-482a-5e81-9036-92c102ec6d79
-- title:
--   Wild inertia: a normal p-subgroup with abelian quotient
-- statement:
--   Let $K$ be a field and $L$ a finite-dimensional Galois extension of $K$, let $A$ be a valuation subring of $L$ whose underlying ring is a discrete valuation ring, and let $p$ be a prime number such that the image of $p$ in $A$ lies in the maximal ideal $\mathfrak m_A$ of $A$. The assertion is that there exists a subgroup $P_w$ of the inertia subgroup $A.\mathrm{inertiaSubgroup}\ K$ (a subgroup of the decomposition subgroup of $A$ over $K$) with the following four properties: first, $P_w$ consists exactly of those $\sigma$ in the inertia subgroup such that for every uniformiser $\varpi$ of $A$ — that is, every irreducible element $\varpi \in A$ — the difference $\sigma\cdot\varpi-\varpi$ lies in $\mathfrak m_A^{2}$; second, $P_w$ is normal in the inertia subgroup; third, $P_w$ is a $p$-group in the sense of `IsPGroup`, i.e. every element has order a power of $p$; and fourth, every commutator $a^{-1}b^{-1}ab$ of elements $a,b$ of the inertia subgroup lies in $P_w$, so that the quotient of the inertia subgroup by $P_w$ is abelian.
--
--   This is the wild inertia (ramification) subgroup of a discrete valuation in a finite Galois extension, described as the set of inertia elements moving every uniformiser only to second order; the statement packages the classical facts that it is normal in inertia, is a $p$-group when the residue characteristic divides $p$, and has abelian (tame) quotient. It is used in the construction of finite étale Galois covers of local rings whose Galois group has a normal $p$-subgroup with abelian quotient, via [`IsDiscreteValuationRing.exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale`](thm.html#IsDiscreteValuationRing.exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_normal_isPGroup_commutator_le_inertiaSubgroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem ValuationSubring.exists_normal_isPGroup_commutator_le_inertiaSubgroup
    (K : Type u) [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing ↥A]
    (p : ℕ) [Fact p.Prime] (hp : (p : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) :
    ∃ Pw : Subgroup ↥(A.inertiaSubgroup K),
      (∀ σ : ↥(A.inertiaSubgroup K), σ ∈ Pw ↔
        ∀ ϖ : ↥A, Irreducible ϖ →
          ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) ∧
      Pw.Normal ∧ IsPGroup p ↥Pw ∧
      ∀ a b : ↥(A.inertiaSubgroup K), a⁻¹ * b⁻¹ * a * b ∈ Pw := by sorry
