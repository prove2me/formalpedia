-- Prove2me | Theorems.Thm_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff
-- name    : ValuationSubring.mem_inertiaSubgroupIn_pointwise_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/8b30c798-f19b-5fd9-83c8-82bee770dcef
-- title:
--   Inertia of a conjugate valuation subring
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $g,\sigma : L \simeq_{\text{alg}[K]} L$ be $K$-algebra automorphisms of $L$, and let $A$ be a valuation subring of $L$. Write $\mathrm{inertiaSubgroupIn}\ K$ for the subgroup of $L \simeq_{\text{alg}[K]} L$ obtained by pushing the inertia subgroup of a valuation subring — the kernel of the action of its decomposition subgroup, i.e. its stabiliser in $L \simeq_{\text{alg}[K]} L$ under the pointwise action on subrings, on the residue field of the local ring in question — forward along the inclusion homomorphism of that decomposition subgroup into the full automorphism group; thus it consists of those automorphisms of $L$ over $K$ which map the valuation subring onto itself and induce the identity on its residue field. Let $g \bullet A$ denote the pointwise image of $A$ under $g$. The assertion is the equivalence: $\sigma$ lies in the inertia subgroup (in this sense) of $g \bullet A$ if and only if $g^{-1}\sigma g$ lies in the inertia subgroup of $A$. Equivalently, the inertia group of $g \bullet A$ is the conjugate $g\,I(A)\,g^{-1}$.
--
--   This is the standard fact that conjugate places of a Galois extension have conjugate inertia groups, in the valuation-subring formulation used throughout the ramification bookkeeping of the project. It is used when a condition on inertia is known at one place above a given rational prime and has to be transported to all the places above it, for instance in the arguments on unipotence on inertia and on deformation rings that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff.lean

import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise

theorem ValuationSubring.mem_inertiaSubgroupIn_pointwise_smul_iff
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (g σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    σ ∈ (g • A).inertiaSubgroupIn K ↔ g⁻¹ * σ * g ∈ A.inertiaSubgroupIn K := by sorry
