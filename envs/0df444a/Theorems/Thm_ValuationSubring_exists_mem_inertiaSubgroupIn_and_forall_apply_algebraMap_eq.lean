-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b13cd27d-ef51-58d6-a345-42a7ab96e4f3
-- title:
--   Lifting inertia along a normal extension
-- statement:
--   Let $K$ be a field and let $L$ and $\Omega$ be fields equipped with $K$-algebra structures, with $\Omega$ also an $L$-algebra compatibly with the $K$-structures (a scalar tower $K \subseteq L \subseteq \Omega$), all three in one universe, and assume $\Omega$ is normal over $K$ (in particular algebraic over $K$). Let $A_0$ be a valuation subring of $L$ and let $\tau$ be a $K$-algebra automorphism of $L$ lying in `A₀.inertiaSubgroupIn K`, i.e. in the image, under the inclusion of the decomposition subgroup of $A_0$ into the full group $L \simeq_{\mathrm{alg}[K]} L$, of the inertia subgroup of $A_0$; concretely, $\tau$ stabilises $A_0$ and acts trivially on its residue field. The assertion is that there exist a valuation subring $A$ of $\Omega$ and a $K$-algebra automorphism $\sigma$ of $\Omega$ such that: the preimage of $A$ under the structure map $L \to \Omega$ is exactly $A_0$; $\sigma$ lies in `A.inertiaSubgroupIn K`, i.e. $\sigma$ stabilises $A$ and induces the identity on the residue field of $A$; and $\sigma$ restricts to $\tau$ along $L \to \Omega$, that is $\sigma(\iota(x)) = \iota(\tau x)$ for all $x \in L$, where $\iota \colon L \to \Omega$ is the structure map.
--
--   This is the inertia-group companion of the classical surjectivity of decomposition groups for a normal extension: inertia elements below are restrictions of inertia elements above, for a suitable choice of valuation ring lying over the given one. It is used in the study of good reduction of elliptic curves over valuation rings, where an inertia element of a base field must be realised as an automorphism of a large normal extension preserving a valuation ring over which torsion points are defined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]
    {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [Normal K Ω]
    (A₀ : ValuationSubring L) (τ : L ≃ₐ[K] L) (hτ : τ ∈ A₀.inertiaSubgroupIn K) :
    ∃ (A : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω),
      A.comap (algebraMap L Ω) = A₀ ∧ σ ∈ A.inertiaSubgroupIn K ∧
        ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω (τ x) := by sorry
