-- Prove2me | Theorems.Thm_PadicComplex_eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul
-- name    : PadicComplex.eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/ad2fb9dd-5d5a-5f00-bb95-4dad7c819317
-- title:
--   Vanishing of ℂₚ(k)^{Gal(ℚ̄ₚ/K)} for k≠ 0
-- statement:
--   Let $p$ be a prime, let `PadicAlgCl p` be the fixed algebraic closure of $\mathbb{Q}_p$ used throughout and $\mathbb{C}_{[p]}$ its completion, carrying the induced action of the group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p`. Let $K$ be an intermediate field between $\mathbb{Q}_p$ and `PadicAlgCl p` which is finite-dimensional over $\mathbb{Q}_p$, let $k$ be a non-zero integer, and let $c \in \mathbb{C}_{[p]}$. Assume that for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of `PadicAlgCl p` belonging to the fixing subgroup of $K$ (that is, fixing every element of $K$) one has
--   $$\sigma \cdot c = \bigl(\iota\bigl(\chi_p(\sigma)\bigr)\bigr)^{k}\, c,$$
--   where $\chi_p(\sigma) \in \mathbb{Z}_p^{\times}$ is the value at the ring automorphism underlying $\sigma$ of Mathlib's cyclotomic character `cyclotomicCharacter (PadicAlgCl p) p`, and $\iota$ denotes the composite of the inclusion $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p$ with the structure map $\mathbb{Q}_p \to \mathbb{C}_{[p]}$, the exponent $k$ being an integer power in $\mathbb{C}_{[p]}$. Then $c = 0$.
--
--   This is Tate's vanishing statement $H^{0}\bigl(\mathrm{Gal}(\overline{\mathbb{Q}}_p/K), \mathbb{C}_p(k)\bigr) = 0$ for $k \neq 0$ and $K/\mathbb{Q}_p$ finite, in the concrete form that a $\mathbb{C}_p$-element transforming under the $k$-th power of the cyclotomic character must vanish. It is used in the theory of $p$-divisible groups over rings of integers of local fields, to pin down the dimension from the Galois action on the Tate module and to show that a $p$-divisible group with trivial inertia action on its Tate module representation has dimension zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicComplex_eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul.lean

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicComplex.eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup →
      σ • c =
        (algebraMap ℚ_[p] ℂ_[p]
            (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k * c) :
    c = 0 := by sorry
