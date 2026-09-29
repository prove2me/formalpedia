-- Prove2me | Theorems.Thm_PadicAlgCl_mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq
-- name    : PadicAlgCl.mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/10d46ba3-c687-5997-a14d-63b291ebe93c
-- title:
--   Fixed points of all 𝒪_K-algebra automorphisms of ℚ̄ₚ
-- statement:
--   Let $p$ be a prime and let $\overline{\mathbb{Q}}_p$ denote the fixed algebraic closure `PadicAlgCl p` of $\mathbb{Q}_p$. Let $K$ be an intermediate field of $\overline{\mathbb{Q}}_p/\mathbb{Q}_p$ which is finite-dimensional over $\mathbb{Q}_p$, and write $\mathcal{O}_K$ for [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the $\mathbb{Z}_p$-subalgebra of $\overline{\mathbb{Q}}_p$ obtained as the intersection of the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$ with $K$, viewed as a $\mathbb{Z}_p$-subalgebra. Let $K'$ be a field equipped with an $\mathcal{O}_K$-algebra structure making it a fraction field of $\mathcal{O}_K$, together with an algebra structure of $\overline{\mathbb{Q}}_p$ over $K'$ for which $\mathcal{O}_K \to K' \to \overline{\mathbb{Q}}_p$ is a tower of scalars (so the composite is the inclusion $\mathcal{O}_K \subseteq \overline{\mathbb{Q}}_p$). The assertion is that if $x \in \overline{\mathbb{Q}}_p$ satisfies $\tau(x) = x$ for every $\mathcal{O}_K$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}}_p$, then $x$ lies in the image of the structure map $K' \to \overline{\mathbb{Q}}_p$.
--
--   This is the "fixed field equals the base" input for Galois descent along $\overline{\mathbb{Q}}_p/K$, stated in the form needed when the base is presented by its ring of integers and an abstract fraction field of it: being fixed by the whole group $\mathrm{Gal}(\overline{\mathbb{Q}}_p/K)$, realised as the group of $\mathcal{O}_K$-algebra automorphisms, forces an element into $K = \mathrm{Frac}\,\mathcal{O}_K$. It is used in the descent step for points of base-changed Hopf-algebra quotient systems attached to $p$-divisible groups, in [`PDivisibleGroup.exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem`](thm.html#PDivisibleGroup.exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq.lean

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K']
    [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
    [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)]
    (x : PadicAlgCl p)
    (hx : ∀ τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p, τ x = x) :
    x ∈ Set.range (algebraMap K' (PadicAlgCl p)) := by sorry
