-- Prove2me | Theorems.Thm_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup
-- name    : PadicAlgCl.norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/b22e043c-f2e5-5754-9798-ed89abfcf847
-- title:
--   Absolute values of ζ-1 and σζ-ζ in the p-cyclotomic tower
-- statement:
--   Let $p$ be a prime and let $\mathrm{PadicAlgCl}\ p$ denote the algebraic closure of $\mathbb{Q}_p$ used throughout, equipped with its norm extending the $p$-adic absolute value. Let $n,k$ be natural numbers with $k<n$, let $\zeta$ be an element of this algebraic closure which is a primitive $p^n$-th root of unity, and let $\sigma$ be a $\mathbb{Q}_p$-algebra automorphism of $\mathrm{PadicAlgCl}\ p$. For each $m$, [`PadicAlgCl.cyclotomicTower p m`](def/PadicAlgCl_CyclotomicTower.html#L9) is the intermediate field $\mathbb{Q}_p\big(\{\xi : \xi^{p^m}=1\}\big)$ obtained by adjoining to $\mathbb{Q}_p$ all $p^m$-th roots of unity, and its fixing subgroup consists of those automorphisms fixing it pointwise. Assume $\sigma$ lies in the fixing subgroup of [`PadicAlgCl.cyclotomicTower p k`](def/PadicAlgCl_CyclotomicTower.html#L9) but not in that of [`PadicAlgCl.cyclotomicTower p (k+1)`](def/PadicAlgCl_CyclotomicTower.html#L9). Then both
--   $$\|\zeta-1\| = p^{-1/\varphi(p^n)} \qquad\text{and}\qquad \|\sigma\zeta-\zeta\| = p^{-1/\varphi(p^{\,n-k})},$$
--   the exponents being real powers of the real number $p$ and $\varphi$ being Euler's totient function (the subtraction $n-k$ is natural-number subtraction, unambiguous here since $k<n$).
--
--   The first equality expresses that $\zeta-1$ is a uniformiser of the totally ramified extension $\mathbb{Q}_p(\zeta)/\mathbb{Q}_p$ of degree $\varphi(p^n)$, and the second measures how far an automorphism moves $\zeta$ in terms of its level in the cyclotomic tower. It is used in the proof of [`PadicAlgCl.exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower`](thm.html#PadicAlgCl.exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower), which produces uniform lower bounds for $\|\sigma x - x\|$ for elements $x$ of a compositum involving the cyclotomic tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup.lean

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup
    (p : ℕ) [Fact p.Prime] {n k : ℕ} (hkn : k < n) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ (PadicAlgCl.cyclotomicTower p k).fixingSubgroup)
    (hσ' : σ ∉ (PadicAlgCl.cyclotomicTower p (k + 1)).fixingSubgroup) :
    ‖ζ - 1‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ n).totient : ℝ)) ∧
      ‖σ ζ - ζ‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ (n - k)).totient : ℝ)) := by sorry
