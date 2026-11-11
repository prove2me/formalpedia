-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_3_2
-- name    : RestrictedAP.Counting.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:53.163325+00:00
-- url     : https://prove2.me/theorems/110201f3-fecf-4fd2-9c42-09fb8bc6a4de
-- title:
--   Lemma 3.2 — a collection of discrete cyclic product functions is symbolically close to one of high rank
-- statement:
--   Let $\mathcal P$ be a collection of $M$-discrete cyclic (normalized) product functions on $\Sigma^n$, let $k=M|\mathcal P|+1$ and let $D_1\le D_2\le\dots\le D_k$ be integers. Then there are a collection $\mathcal P'$ of $M$-discrete cyclic product functions with $|\mathcal P'|\le|\mathcal P|$ and an index $1\le i\le k$ such that
--
--   1. $\mathrm{rk}(\mathcal P')\ge D_i$;
--   2. $\Delta_{\rm symbolic}(P,\mathrm{span}_{\mathbb N}(\mathcal P'))\le D_1+\dots+D_{i-1}$ for each $P\in\mathcal P$;
--   3. $\Delta_{\rm symbolic}(P',\mathrm{span}_{\mathbb N}(\mathcal P))\le D_1+\dots+D_{i-1}$ for each $P'\in\mathcal P'$.
--
--   It is the rank-raising step of the regularity argument: the rank achieved can be made arbitrarily large compared with the symbolic cost of the modification.
--
--   Differences from the source:
--   - reading: product functions (the theorem's sentence) → product functions normalized at a distinguished σ⋆: factors of modulus 1 with P_i(σ⋆) = 1 (`IsProductFunction σs`); reason: §2.1 (p. 7): 'Unless specified otherwise, throughout this paper we will consider normalized product functions'
--   - encoding: integers D_1 ≤ D_2 ≤ … ≤ D_k and D_1 + … + D_{i−1} → `D : ℕ → ℤ` monotone on indices 1..k (D 0 unused) and `∑ j ∈ Finset.Ico 1 i, D j`; reason: 1-based indexing of the printed sequence
--   - encoding: a collection 𝒫 of product functions and |𝒫| → a `Finset` of functions `(Fin n → Σ) → ℂ` and its card; reason: a collection is a set of functions
--   - encoding: ord(P) ∈ ℕ ∪ {∞} → `orderOf P` in the monoid of functions (0 encodes ∞); M-discrete = 0 < orderOf P ≤ M; reason: Mathlib's order of an element is the least k ≥ 1 with P^k = 1, as Definition 2.3
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), pp. 15–16, Lemma 3.2

import Mathlib
import Definitions.Def_RestrictedAP_Counting_ProductFunctions

namespace RestrictedAP.Counting

/-- **Lemma 3.2** (pp. 15–16). Let `𝒫` be a collection of `M`-discrete cyclic (normalized) product
functions, `k = M|𝒫| + 1`, and `D_1 ≤ D_2 ≤ … ≤ D_k` integers. Then there are a collection `𝒫'`
of `M`-discrete cyclic product functions with `|𝒫'| ≤ |𝒫|` and `1 ≤ i ≤ k` such that
1. `rk(𝒫') ≥ D_i`;
2. `Δ_symbolic(P, span_ℕ(𝒫')) ≤ D_1 + … + D_{i−1}` for each `P ∈ 𝒫`;
3. `Δ_symbolic(P', span_ℕ(𝒫)) ≤ D_1 + … + D_{i−1}` for each `P' ∈ 𝒫'`.
The integers `D_j` are `D j` for `j = 1, …, k` (the value `D 0` is unused). -/
theorem lemma_3_2 (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (n M : ℕ)
    (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P)
    (D : ℕ → ℤ) (hD : ∀ j, 1 ≤ j → j < M * PP.card + 1 → D j ≤ D (j + 1)) :
    ∃ PP' : Finset ((Fin n → Sig) → ℂ),
      (∀ P ∈ PP', IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) ∧
      PP'.card ≤ PP.card ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ M * PP.card + 1 ∧
        RankAtLeast PP' (D i : ℝ) ∧
        (∀ P ∈ PP, (distToSpan P PP' : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j) ∧
        (∀ P ∈ PP', (distToSpan P PP : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j) := by sorry

end RestrictedAP.Counting
