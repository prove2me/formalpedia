-- Prove2me | Theorems.Thm_ValuationSubring_mem_decompositionSubgroup_of_forall_mem_fixedField_inf_separableClosure_imp_eq
-- name    : ValuationSubring.mem_decompositionSubgroup_of_forall_mem_fixedField_inf_separableClosure_imp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/539bc818-6349-50db-b5d0-f943ee947312
-- title:
--   Fixing the separable decomposition field forces stabilisation of A
-- statement:
--   Let $K$ be a field and let $\Omega$ be an algebraic closure of $K$ (a field with a $K$-algebra structure satisfying `IsAlgClosure K Ω`, both in the same universe). Let $A$ be a valuation subring of $\Omega$, let $K'$ be an intermediate field of $\Omega/K$, and let $\tau$ be a $K$-algebra automorphism of $\Omega$. Write $H :=$ `A.decompositionSubgroup K ⊓ K'.fixingSubgroup` for the subgroup of $\operatorname{Aut}_K(\Omega)$ consisting of those automorphisms that stabilise $A$ setwise (membership in the decomposition subgroup is, by definition, membership in the stabiliser of $A$ for the pointwise action) and fix $K'$ pointwise. Assume that $\tau x = x$ for every $x \in \Omega$ lying in the intersection, formed in the lattice of intermediate fields of $\Omega/K$, of the fixed field of $H$ with the separable closure of $K'$ in $\Omega$ viewed as an intermediate field of $\Omega/K$ by restriction of scalars. The conclusion is that $\tau$ lies in `A.decompositionSubgroup K`, that is, $\tau \bullet A = A$.
--
--   This is the Galois correspondence for decomposition groups at the level of an algebraic closure: the decomposition group of $A$ over $K'$ is recovered as the group of automorphisms fixing the separable part of its fixed field, the separable closure being needed because a valuation subring is insensitive to purely inseparable extensions. It is used in the construction of an intermediate field over which the contracted valuation ring is a Henselian discrete valuation ring, in [`ValuationSubring.exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional`](thm.html#ValuationSubring.exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_mem_decompositionSubgroup_of_forall_mem_fixedField_inf_separableClosure_imp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ValuationSubring.mem_decompositionSubgroup_of_forall_mem_fixedField_inf_separableClosure_imp_eq
    {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (K' : IntermediateField K Ω)
    (τ : Ω ≃ₐ[K] Ω)
    (hτ : ∀ x : Ω,
      x ∈ IntermediateField.fixedField (A.decompositionSubgroup K ⊓ K'.fixingSubgroup) ⊓
        (separableClosure ↥K' Ω).restrictScalars K →
      τ x = x) :
    τ ∈ A.decompositionSubgroup K := by sorry
