-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_3_4
-- name    : RestrictedAP.Counting.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:47.60996+00:00
-- url     : https://prove2.me/theorems/a74bcd83-ca79-464a-a78e-286e891f6d1a
-- title:
--   Lemma 3.4 — high rank and high softrank simultaneously, at small symbolic cost
-- statement:
--   For all $r$ and $M$ there is $k=k(r,M)$ such that the following holds. Let $\Sigma$ be a finite alphabet, $\mu$ a distribution on $\Sigma^3$ and $\mathcal P$ a collection of $r$ $M$-discrete cyclic (normalized) product functions on $\Sigma^n$. For all integers $D_1\le\dots\le D_k$ there are $1\le i\le k$ and a collection $\mathcal P'$ of $M$-discrete cyclic product functions with $|\mathcal P'|\le|\mathcal P|$ such that
--
--   1. $\mathrm{softrk}_\mu(\mathcal P')$ and $\mathrm{rk}(\mathcal P')$ are both at least $D_i-(D_1+\dots+D_{i-1})$;
--   2. $\Delta_{\rm symbolic}(P,\mathrm{span}_{\mathbb N}(\mathcal P'))\le2(D_1+\dots+D_{i-1})$ for each $P\in\mathcal P$;
--   3. $\Delta_{\rm symbolic}(P',\mathrm{span}_{\mathbb N}(\mathcal P))\le2(D_1+\dots+D_{i-1})$ for each $P'\in\mathcal P'$.
--
--   Differences from the source:
--   - reading: there exists k = k(|𝒫|, M) → ∃ k after r = |𝒫| and M, before Σ, μ, n, 𝒫 (with |𝒫| = r); reason: the printed dependence of k
--   - reading: product functions (the theorem's sentence) → product functions normalized at a distinguished σ⋆: factors of modulus 1 with P_i(σ⋆) = 1 (`IsProductFunction σs`); reason: §2.1 (p. 7): 'Unless specified otherwise, throughout this paper we will consider normalized product functions'
--   - encoding: integers D_1 ≤ D_2 ≤ … ≤ D_k and D_1 + … + D_{i−1} → `D : ℕ → ℤ` monotone on indices 1..k (D 0 unused) and `∑ j ∈ Finset.Ico 1 i, D j`; reason: 1-based indexing of the printed sequence
--   - encoding: a collection 𝒫 of product functions and |𝒫| → a `Finset` of functions `(Fin n → Σ) → ℂ` and its card; reason: a collection is a set of functions
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 17, Lemma 3.4

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions

namespace RestrictedAP.Counting

/-- **Lemma 3.4** (p. 17). For all `r` (the size `|𝒫|`) and `M` there is `k = k(r, M)` such that:
for every finite alphabet `Σ`, distribution `μ` on `Σ^3`, and collection `𝒫` of `r` `M`-discrete
cyclic (normalized) product functions, and all integers `D_1 ≤ … ≤ D_k`, there are `1 ≤ i ≤ k`
and a collection `𝒫'` of `M`-discrete cyclic product functions with `|𝒫'| ≤ |𝒫|` such that
1. `softrk_μ(𝒫')` and `rk(𝒫')` are both at least `D_i − (D_1 + … + D_{i−1})`;
2. `Δ_symbolic(P, span_ℕ(𝒫')) ≤ 2(D_1 + … + D_{i−1})` for each `P ∈ 𝒫`;
3. `Δ_symbolic(P', span_ℕ(𝒫)) ≤ 2(D_1 + … + D_{i−1})` for each `P' ∈ 𝒫'`. -/
theorem lemma_3_4 (r M : ℕ) :
    ∃ k : ℕ, ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig)
      (μ : Sig × Sig × Sig → ℝ) (n : ℕ) (PP : Finset ((Fin n → Sig) → ℂ)),
      IsDist μ → PP.card = r →
      (∀ P ∈ PP, IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) →
      ∀ D : ℕ → ℤ, (∀ j, 1 ≤ j → j < k → D j ≤ D (j + 1)) →
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ k ∧
        ∃ PP' : Finset ((Fin n → Sig) → ℂ),
          (∀ P ∈ PP', IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) ∧
          PP'.card ≤ PP.card ∧
          SoftRankMuAtLeast μ PP' ((D i - ∑ j ∈ Finset.Ico 1 i, D j : ℤ) : ℝ) ∧
          RankAtLeast PP' ((D i - ∑ j ∈ Finset.Ico 1 i, D j : ℤ) : ℝ) ∧
          (∀ P ∈ PP, (distToSpan P PP' : ℤ) ≤ 2 * ∑ j ∈ Finset.Ico 1 i, D j) ∧
          (∀ P ∈ PP', (distToSpan P PP : ℤ) ≤ 2 * ∑ j ∈ Finset.Ico 1 i, D j) := by sorry

end RestrictedAP.Counting
