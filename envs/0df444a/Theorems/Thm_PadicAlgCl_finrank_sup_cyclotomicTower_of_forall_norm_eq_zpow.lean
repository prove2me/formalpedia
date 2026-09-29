-- Prove2me | Theorems.Thm_PadicAlgCl_finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow
-- name    : PadicAlgCl.finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/c1c73239-624b-5ff4-ab47-6072d0e6b7d5
-- title:
--   Degree of K·ℚₚ(μ_{pⁿ}) for absolutely unramified K
-- statement:
--   Let $p$ be a prime and let $\mathbb{C}_p^{\mathrm{alg}} =$ `PadicAlgCl p` be the fixed algebraic closure of $\mathbb{Q}_p$ used throughout. Let $K$ be an intermediate field of the extension $\mathbb{Q}_p \subseteq$ `PadicAlgCl p` which is finite-dimensional over $\mathbb{Q}_p$, and assume that the norm inherited from the algebraic closure takes values in $p^{\mathbb{Z}}$ on $K$: for every $x \in K$ with $x \neq 0$ there is an integer $k$ with $\|x\| = p^{k}$. Let $n$ be a natural number with $n > 0$. For such $n$, [`PadicAlgCl.cyclotomicTower p n`](def/PadicAlgCl_CyclotomicTower.html#L9) denotes the intermediate field obtained by adjoining to $\mathbb{Q}_p$ the set of all $\zeta \in$ `PadicAlgCl p` with $\zeta^{p^{n}} = 1$, i.e. the field $\mathbb{Q}_p(\mu_{p^n})$. The assertion is that the join (compositum) $K \sqcup \mathbb{Q}_p(\mu_{p^n})$ in the lattice of intermediate fields satisfies $$[\,K \cdot \mathbb{Q}_p(\mu_{p^n}) : \mathbb{Q}_p\,] = [K : \mathbb{Q}_p]\cdot (p-1)p^{\,n-1},$$ the degrees being `Module.finrank` over $\mathbb{Q}_p$ and the right-hand factors being computed in $\mathbb{N}$ (so $p-1$ and $n-1$ are truncated differences, harmless for $p$ prime and $n > 0$).
--
--   This is the standard statement that an absolutely unramified finite extension of $\mathbb{Q}_p$ is linearly disjoint from the totally ramified cyclotomic extension $\mathbb{Q}_p(\mu_{p^n})$, equivalently $[K(\mu_{p^n}):K] = \varphi(p^n)$ and $K \cap \mathbb{Q}_p(\mu_{p^n}) = \mathbb{Q}_p$ (Serre, Local Fields IV §4). It uses the degree computation $[\mathbb{Q}_p(\mu_{p^n}):\mathbb{Q}_p] = (p-1)p^{n-1}$ from [`PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup`](thm.html#PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup), and feeds the norm computation in [`PadicAlgCl.exists_nnnorm_pow_sub_one_eq_zpow_of_mem_adjoin_rootsOfUnity_coprime_sup_cyclotomicTower`](thm.html#PadicAlgCl.exists_nnnorm_pow_sub_one_eq_zpow_of_mem_adjoin_rootsOfUnity_coprime_sup_cyclotomicTower).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow.lean

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (hK : ∀ x ∈ K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (p : ℝ) ^ k) (n : ℕ) (hn : 0 < n) :
    Module.finrank ℚ_[p] ↥(K ⊔ PadicAlgCl.cyclotomicTower p n) =
      Module.finrank ℚ_[p] K * ((p - 1) * p ^ (n - 1)) := by sorry
