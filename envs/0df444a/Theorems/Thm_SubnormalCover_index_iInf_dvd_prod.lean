-- Prove2me | Theorems.Thm_SubnormalCover_index_iInf_dvd_prod
-- name    : SubnormalCover.index_iInf_dvd_prod
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:43:28.247092+00:00
-- url     : https://prove2.me/theorems/30f78335-e2ea-4ba6-a0e1-c4b53edef542
-- title:
--   Index of an intersection of subnormal subgroups
-- statement:
--   Let $G$ be a group and let $K_1,\dots,K_k$ be **subnormal** subgroups of $G$, each of finite index. Then the index of their intersection divides the product of the individual indices: $\bigl[G:\bigcap_{i=1}^{k}K_i\bigr] \;\Bigm|\; \prod_{i=1}^{k}[G:K_i]$, and consequently $P\bigl([G:\bigcap_i K_i]\bigr)=\bigcup_i P([G:K_i])$ for the sets of prime divisors. Subnormality is essential: for arbitrary finite-index subgroups Poincaré's theorem gives only the inequality $[G:\bigcap_i K_i]\le\prod_i[G:K_i]$, and divisibility fails already for the two subgroups $\langle(12)\rangle,\langle(13)\rangle$ of $S_3$, where the intersection is trivial of index $6$ while $3\cdot 3=9$. This arithmetic property of subnormality is the reason covers by subnormal subgroups are far better behaved than general coset covers. *Formalization note:* the family is indexed by `Fin k`, the intersection is the lattice infimum `⨅ i, K i`, and "finite index" is the class `Subgroup.FiniteIndex` supplied as a plain hypothesis `∀ i, (K i).FiniteIndex` (equivalently `(K i).index ≠ 0`), so a prover must `haveI` it before instance search can use it.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Lemma 2.1, eq. (2.1) (restated from Lemma 3.1(ii) of [Su8])

import Mathlib

namespace SubnormalCover

/-- **Sun, Lemma 2.1 / equation (2.1).**

If `K 1, …, K k` are *subnormal* subgroups of finite index of a group `G`, then the index of
their intersection divides the product of their indices:
`[G : ⋂ᵢ Kᵢ] ∣ ∏ᵢ [G : Kᵢ]`.

For arbitrary (non-subnormal) finite-index subgroups, Poincaré's theorem only gives the
inequality `[G : ⋂ᵢ Kᵢ] ≤ ∏ᵢ [G : Kᵢ]` (`Subgroup.index_iInf_le`); divisibility genuinely
requires subnormality. -/
theorem index_iInf_dvd_prod {G : Type*} [Group G] {k : ℕ} (K : Fin k → Subgroup G)
    (hsn : ∀ i, (K i).IsSubnormal) (hfin : ∀ i, (K i).FiniteIndex) :
    (⨅ i, K i).index ∣ ∏ i, (K i).index := by
  sorry

end SubnormalCover
