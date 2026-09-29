-- Prove2me | Theorems.Thm_PadicComplex_exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers
-- name    : PadicComplex.exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/679c01c7-b575-5edb-88c5-67e8b5482a29
-- title:
--   Unit period for the determinant of an unramified representation
-- statement:
--   Fix a prime $p$ and let $K$ be an intermediate field of $\mathbb{Q}_p \subseteq \overline{\mathbb{Q}}_p$ (the algebraic closure `PadicAlgCl p`) that is finite-dimensional over $\mathbb{Q}_p$; write $\mathcal{O}_K$ for [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the $\mathbb{Z}_p$-subalgebra of $\overline{\mathbb{Q}}_p$ consisting of those elements that are integral over $\mathbb{Z}_p$ and lie in $K$. Let $T$ be an abelian group with a finite free $\mathbb{Z}_p$-module structure and let $\rho$ be a monoid homomorphism from the group of $\mathcal{O}_K$-algebra automorphisms of $\overline{\mathbb{Q}}_p$ to the $\mathbb{Z}_p$-linear endomorphisms of $T$. Two hypotheses are imposed, both phrased through pairs $(\sigma,\tau)$ where $\sigma$ is a $\mathbb{Q}_p$-algebra automorphism of $\overline{\mathbb{Q}}_p$, $\tau$ an $\mathcal{O}_K$-algebra automorphism, and $\tau t = \sigma t$ for all $t \in \overline{\mathbb{Q}}_p$: first, unramifiedness, that $\rho\tau = 1$ whenever $\sigma$ lies in `inertiaSubgroupIn ℚ_[p]` of the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) of $\overline{\mathbb{Q}}_p$, that is, in the image of the inertia subgroup of that valuation subring under the inclusion of its decomposition subgroup; second, continuity, that for every $n \in \mathbb{N}$ there is an intermediate field $K'$ of $\mathbb{Q}_p \subseteq \overline{\mathbb{Q}}_p$, finite over $\mathbb{Q}_p$, such that whenever $\sigma$ fixes $K'$ pointwise one has $\rho\tau\, t - t \in p^n T$ for all $t \in T$. The conclusion is that there exists $u \in \mathbb{C}_p$ with $u \neq 0$ such that for every such pair $(\sigma,\tau)$ one has $\sigma \cdot u = \det(\rho\tau)\, u$, the determinant being taken in $\mathbb{Z}_p$ and mapped into $\mathbb{C}_p$ through $\mathbb{Q}_p$.
--
--   This is the rank-one, or determinant, form of the statement that an unramified $p$-adic representation becomes trivial over $\mathbb{C}_p$: the unramified character $\det \circ \rho$ admits a non-zero period in $\mathbb{C}_p$. It is used in the proof that a $p$-divisible group whose Tate module is unramified has dimension zero, via [`PDivisibleGroup.hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers`](thm.html#PDivisibleGroup.hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicComplex_exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PadicComplex.exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
    (ρ : (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) →* Module.End ℤ_[p] T)

    (hunr : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) → σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ρ τ = 1)

    (hcont : ∀ n : ℕ, ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K' ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
          (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
          (∀ t : PadicAlgCl p, τ t = σ t) → σ ∈ K'.fixingSubgroup →
          ∀ t : T, ∃ s : T, ρ τ t - t = ((p : ℤ_[p]) ^ n) • s) :
    ∃ u : ℂ_[p], u ≠ 0 ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) →
        σ • u = algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (LinearMap.det (ρ τ))) * u := by sorry
