-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_forall_exists_div_mem_units
-- name    : ValuationSubring.isDiscreteValuationRing_comap_of_forall_exists_div_mem_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/a60558da-66a7-55e3-a984-b9fcb4346406
-- title:
--   Discreteness descends to intermediate fields with the same values
-- statement:
--   Let $L$ and $\Omega$ be fields, both in the same universe, with $\Omega$ an $L$-algebra, and let $A$ be a valuation subring of $\Omega$. Assume that the preimage `A.comap (algebraMap L Ω)`, the valuation subring of $L$ consisting of those $c$ with $\mathrm{algebraMap}_{L,\Omega}(c) \in A$, is a discrete valuation ring. Let $M$ be an intermediate field of $\Omega/L$ and assume that for every $x \in \Omega$ lying in $M$ and non-zero there exists $c \in L$, $c \neq 0$, such that both $x \cdot \mathrm{algebraMap}_{L,\Omega}(c)^{-1} \in A$ and $\mathrm{algebraMap}_{L,\Omega}(c) \cdot x^{-1} \in A$ — that is, $x$ and the image of $c$ have the same value, their ratio being a unit of $A$. The conclusion is that the valuation subring `A.comap (algebraMap ↥M Ω)` of $M$, consisting of the elements of $M$ whose image in $\Omega$ lies in $A$, is again a discrete valuation ring.
--
--   This is the valuation-theoretic statement that a valuation ring whose value group coincides with that of a discrete valuation subring is itself a discrete valuation ring: a uniformiser of $A \cap L$ remains a uniformiser of $A \cap M$. It feeds the more specialised criterion [`ValuationSubring.isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq`](thm.html#ValuationSubring.isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq), part of the infrastructure on discretely valued intermediate fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_comap_of_forall_exists_div_mem_units.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ValuationSubring.isDiscreteValuationRing_comap_of_forall_exists_div_mem_units
    {L : Type u} [Field L] {Ω : Type u} [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap L Ω)))
    (M : IntermediateField L Ω)
    (hval : ∀ x : Ω, x ∈ M → x ≠ 0 →
      ∃ c : L, c ≠ 0 ∧ x * (algebraMap L Ω c)⁻¹ ∈ A ∧ algebraMap L Ω c * x⁻¹ ∈ A) :
    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥M Ω)) := by sorry
