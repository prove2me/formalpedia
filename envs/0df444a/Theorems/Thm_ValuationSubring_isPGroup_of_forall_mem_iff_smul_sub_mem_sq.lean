-- Prove2me | Theorems.Thm_ValuationSubring_isPGroup_of_forall_mem_iff_smul_sub_mem_sq
-- name    : ValuationSubring.isPGroup_of_forall_mem_iff_smul_sub_mem_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/09771180-e75d-5991-a52c-1c668343b4b2
-- title:
--   Wild inertia is a p-group at a discrete place
-- statement:
--   Let $K$ be a field and $L$ a finite Galois extension of $K$, and let $A$ be a valuation subring of $L$ whose underlying ring is a discrete valuation ring; write $\mathfrak m$ for its maximal ideal. Let $p$ be a prime whose image in $A$ lies in $\mathfrak m$, so that the residue field of $A$ has characteristic $p$. Let $P_w$ be a subgroup of the inertia subgroup $A.\mathrm{inertiaSubgroup}\ K$ of $A$ over $K$, and assume that $P_w$ is characterised inside the inertia group as follows: an element $\sigma$ of the inertia subgroup belongs to $P_w$ if and only if for every irreducible element $\varpi$ of $A$ (that is, every uniformiser) the difference $\sigma\cdot\varpi-\varpi$, formed using the action of $\sigma$ regarded as an element of the decomposition subgroup of $A$ over $K$ on $A$, lies in $\mathfrak m^2$. The conclusion is that $P_w$ is a $p$-group in the sense of `IsPGroup`: every element of $P_w$ has order a power of $p$.
--
--   This is the statement that the wild part of inertia at a discretely valued place of residue characteristic $p$ — here described as the kernel of the character sending $\sigma$ to the unit $\sigma(\varpi)/\varpi$ modulo $\mathfrak m$, i.e. the subgroup acting trivially on $\mathfrak m/\mathfrak m^2$ — is a $p$-group, with no separability assumption on the residue extension. It is used in [`ValuationSubring.exists_normal_isPGroup_commutator_le_inertiaSubgroup`](thm.html#ValuationSubring.exists_normal_isPGroup_commutator_le_inertiaSubgroup) to split off a normal $p$-subgroup of the inertia group with abelian, hence tame, quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isPGroup_of_forall_mem_iff_smul_sub_mem_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem ValuationSubring.isPGroup_of_forall_mem_iff_smul_sub_mem_sq
    (K : Type u) [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing ↥A]
    (p : ℕ) [Fact p.Prime] (hp : (p : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)
    (Pw : Subgroup ↥(A.inertiaSubgroup K))
    (hPw : ∀ σ : ↥(A.inertiaSubgroup K), σ ∈ Pw ↔
        ∀ ϖ : ↥A, Irreducible ϖ →
          ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) :
    IsPGroup p ↥Pw := by sorry
