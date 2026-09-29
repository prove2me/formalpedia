-- Prove2me | Theorems.Thm_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup
-- name    : PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/be0695f7-fd12-531d-b17d-d065b24548c6
-- title:
--   Degrees in the p-power cyclotomic tower over ℚₚ
-- statement:
--   Let $p$ be a prime, and for each $n$ let $F_n \subseteq \mathrm{PadicAlgCl}\,p$ denote [`PadicAlgCl.cyclotomicTower p n`](def/PadicAlgCl_CyclotomicTower.html#L9), the intermediate field of the extension $\mathrm{PadicAlgCl}\,p/\mathbb{Q}_p$ obtained by adjoining to $\mathbb{Q}_p$ the set of all $\zeta$ in $\mathrm{PadicAlgCl}\,p$ with $\zeta^{p^n} = 1$, i.e. $F_n = \mathbb{Q}_p(\mu_{p^n})$ inside the chosen algebraic closure `PadicAlgCl p` of $\mathbb{Q}_p$. The theorem is the conjunction of two assertions. First, for every $n > 0$ the $\mathbb{Q}_p$-vector space $F_n$ has finite rank $(p-1)p^{n-1}$, the subtractions being those of $\mathbb{N}$. Second, for every natural number $m$ and every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\mathrm{PadicAlgCl}\,p$: if $\sigma$ lies in the fixing subgroup of $F_{m+2}$ (that is, $\sigma$ fixes $F_{m+2}$ pointwise) but not in the fixing subgroup of $F_{m+3}$, then $\sigma^p$ lies in the fixing subgroup of $F_{m+3}$ and does not lie in the fixing subgroup of $F_{m+4}$. Thus an element of $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p(\mu_{p^{m+2}}))$ acting non-trivially on $\mu_{p^{m+3}}$ has $p$-th power acting trivially on $\mu_{p^{m+3}}$ and non-trivially on $\mu_{p^{m+4}}$.
--
--   The first clause is the classical degree formula $[\mathbb{Q}_p(\mu_{p^n}):\mathbb{Q}_p] = \varphi(p^n)$, equivalent to the irreducibility of $\Phi_{p^n}$ over $\mathbb{Q}_p$; the second records that, in the tower $F_m = \mathbb{Q}_p(\mu_{p^{m+2}})$ of degree-$p$ steps, the $p$-th power of a generator of $\mathrm{Gal}(F_{m+1}/F_m)$ generates $\mathrm{Gal}(F_{m+2}/F_{m+1})$. Both clauses feed the local estimates on cyclotomic towers used later, such as [`PadicAlgCl.finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow`](thm.html#PadicAlgCl.finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow) and [`PadicAlgCl.norm_sum_pow_apply_le_of_mem_cyclotomicTower`](thm.html#PadicAlgCl.norm_sum_pow_apply_le_of_mem_cyclotomicTower).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup.lean

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup (p : ℕ) [Fact p.Prime] :
    (∀ n : ℕ, 0 < n →
      Module.finrank ℚ_[p] (PadicAlgCl.cyclotomicTower p n) = (p - 1) * p ^ (n - 1)) ∧
    (∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      σ ∈ (PadicAlgCl.cyclotomicTower p (m + 2)).fixingSubgroup →
      σ ∉ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup →
        σ ^ p ∈ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup ∧
          σ ^ p ∉ (PadicAlgCl.cyclotomicTower p (m + 4)).fixingSubgroup) := by sorry
