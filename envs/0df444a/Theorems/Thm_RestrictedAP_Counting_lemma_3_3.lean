-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_3_3
-- name    : RestrictedAP.Counting.lemma_3_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:49.284765+00:00
-- url     : https://prove2.me/theorems/82bef109-68d6-476b-a5a3-f21d93bea50f
-- title:
--   Lemma 3.3 — projecting off few coordinates gives high softrank
-- statement:
--   Let $\Sigma$ be a finite alphabet, $\mu$ a distribution on $\Sigma^3$, $\mathcal P$ a collection of $M$-discrete cyclic (normalized) product functions on $\Sigma^n$, and $k=M^{3|\mathcal P|}$. Then for all integers $D_1\le\dots\le D_k$ there are $1\le i\le k$ and $J\subseteq[n]$ with
--
--   1. $|J|\le D_1+\dots+D_{i-1}$;
--   2. $\mathrm{softrk}_\mu(\mathcal P|_{\bar J})\ge D_i$.
--
--   Here $\mathcal P|_{\bar J}=\{P|_{\bar J}:P\in\mathcal P\}$ uses the normalized factors of each $P$.
--
--   Differences from the source:
--   - reading: product functions (the theorem's sentence) → product functions normalized at a distinguished σ⋆: factors of modulus 1 with P_i(σ⋆) = 1 (`IsProductFunction σs`); reason: §2.1 (p. 7): 'Unless specified otherwise, throughout this paper we will consider normalized product functions'
--   - encoding: integers D_1 ≤ D_2 ≤ … ≤ D_k and D_1 + … + D_{i−1} → `D : ℕ → ℤ` monotone on indices 1..k (D 0 unused) and `∑ j ∈ Finset.Ico 1 i, D j`; reason: 1-based indexing of the printed sequence
--   - encoding: a collection 𝒫 of product functions and |𝒫| → a `Finset` of functions `(Fin n → Σ) → ℂ` and its card; reason: a collection is a set of functions
--   - encoding: J̄ and P|_{J̄} : Σ^n → D → `Jᶜ` and `proj σs Jᶜ P = ∏_{i ∉ J} P(σ⋆,…,x_i,…,σ⋆)`; reason: Definition 2.2 with the normalized decomposition
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 16, Lemma 3.3

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions

namespace RestrictedAP.Counting

/-- **Lemma 3.3** (p. 16). Let `Σ` be a finite alphabet, `μ` a distribution on `Σ^3`, `𝒫` a
collection of `M`-discrete cyclic (normalized) product functions, and `k = M^{3|𝒫|}`. Then for
all integers `D_1 ≤ … ≤ D_k` there are `1 ≤ i ≤ k` and `J ⊆ [n]` with
1. `|J| ≤ D_1 + … + D_{i−1}`;
2. `softrk_μ(𝒫|_{J̄}) ≥ D_i`.
The integers `D_j` are `D j` for `j = 1, …, k`. -/
theorem lemma_3_3 (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig)
    (μ : Sig × Sig × Sig → ℝ) (hμ : IsDist μ) (n M : ℕ)
    (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P)
    (D : ℕ → ℤ) (hD : ∀ j, 1 ≤ j → j < M ^ (3 * PP.card) → D j ≤ D (j + 1)) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ M ^ (3 * PP.card) ∧
      ∃ J : Finset (Fin n), (J.card : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j ∧
        SoftRankMuAtLeast μ (projColl σs Jᶜ PP) (D i : ℝ) := by sorry

end RestrictedAP.Counting
