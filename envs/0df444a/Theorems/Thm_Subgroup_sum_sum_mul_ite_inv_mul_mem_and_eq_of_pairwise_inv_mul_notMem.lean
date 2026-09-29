-- Prove2me | Theorems.Thm_Subgroup_sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem
-- name    : Subgroup.sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/72c5dfb3-4e10-5255-b588-d01c03dfdd9c
-- title:
--   Exactly one coset cell contributes to a double sum
-- statement:
--   Let $G$ be a group, let $A$ and $V$ be subgroups of $G$, let $F_a$ and $F_t$ be finite subsets of $G$, and let $c : G \to G \to \mathbb{C}$ be a coefficient function. Assume that the elements of $F_a$ are pairwise inequivalent modulo $A$ on the left, in the sense that $\alpha^{-1}\alpha' \notin A$ whenever $\alpha, \alpha' \in F_a$ and $\alpha \neq \alpha'$, and likewise that $\tau^{-1}\tau' \notin V$ whenever $\tau, \tau' \in F_t$ and $\tau \neq \tau'$. Let $a, t, \alpha, \tau \in G$ with $\alpha \in F_a$, $\tau \in F_t$, $a^{-1}\alpha \in A$ and $t^{-1}\tau \in V$. Then the double sum over $\alpha' \in F_a$ and $\tau' \in F_t$ of $c(\alpha',\tau')$ multiplied by the indicator, equal to $1$ or $0$, of the condition $a^{-1}\alpha' \in A$ and $t^{-1}\tau' \in V$ equals $c(\alpha,\tau)$. Decidability of the conditions is supplied classically.
--
--   This is the selection principle for a step function built on a grid of cells indexed by representatives of left cosets: at a point $(a,t)$ lying in the cell of $(\alpha,\tau)$ exactly one indicator fires, so the sum reads off the corresponding coefficient. It is used in the construction of the local window functions entering [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Classical in

theorem Subgroup.sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem
    {G : Type*} [Group G] (A V : Subgroup G) (Fa Ft : Finset G) (c : G → G → ℂ)
    (hFa : ∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A)
    (hFt : ∀ τ ∈ Ft, ∀ τ' ∈ Ft, τ ≠ τ' → τ⁻¹ * τ' ∉ V)
    (a t α τ : G) (hα : α ∈ Fa) (hτ : τ ∈ Ft) (hA : a⁻¹ * α ∈ A) (hV : t⁻¹ * τ ∈ V) :
    (∑ α' ∈ Fa, ∑ τ' ∈ Ft, c α' τ' * (if a⁻¹ * α' ∈ A ∧ t⁻¹ * τ' ∈ V then 1 else 0)) = c α τ := by sorry
