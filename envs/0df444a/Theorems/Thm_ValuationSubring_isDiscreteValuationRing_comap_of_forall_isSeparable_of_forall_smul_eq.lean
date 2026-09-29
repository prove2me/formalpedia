-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq
-- name    : ValuationSubring.isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/a6b56697-574a-5ba7-a8a9-e60e9982cae6
-- title:
--   Separable subfields fixed by the decomposition group carry DVRs
-- statement:
--   Let $L$ be a field and $\Omega$ a field equipped with an $L$-algebra structure making it an algebraic closure of $L$ (`IsAlgClosure L Ω`), and let $A$ be a valuation subring of $\Omega$. Assume that the preimage of $A$ under the structure map $L \to \Omega$, i.e. the valuation subring $A \cap L$ of $L$, is a discrete valuation ring. Let $M$ be an intermediate field of $\Omega/L$ subject to two conditions: every element $x \in M$ is separable over $L$, and every $L$-algebra automorphism $\sigma$ of $\Omega$ lying in the decomposition subgroup of $A$ over $L$ — that is, in the stabiliser of $A$ for the natural action of $\mathrm{Aut}_L(\Omega)$ on valuation subrings of $\Omega$ — fixes every element of $M$. The conclusion is that the preimage of $A$ under the structure map $M \to \Omega$, i.e. the valuation subring $A \cap M$ of $M$, is again a discrete valuation ring.
--
--   This is the statement that the decomposition field of $A$ over $L$, taken inside the separable closure, is an immediate extension of the discretely valued field $(L, A \cap L)$: every separable subextension fixed by the decomposition group again has value group $\mathbb{Z}$, so its valuation ring is discrete. Separability cannot be dropped, as the perfect hull $L^{1/p^{\infty}}$ is fixed by all automorphisms yet has $p$-divisible value group; the result feeds the construction of an intermediate field whose associated valuation ring is a henselian discrete valuation ring, used on the $R = T$ route.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ValuationSubring.isDiscreteValuationRing_comap_of_forall_isSeparable_of_forall_smul_eq
    {L : Type u} [Field L] {Ω : Type u} [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (A : ValuationSubring Ω)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap L Ω)))
    (M : IntermediateField L Ω)
    (hsep : ∀ x : Ω, x ∈ M → IsSeparable L x)
    (hfix : ∀ σ : Ω ≃ₐ[L] Ω, σ ∈ A.decompositionSubgroup L → ∀ x : Ω, x ∈ M → σ x = x) :
    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥M Ω)) := by sorry
