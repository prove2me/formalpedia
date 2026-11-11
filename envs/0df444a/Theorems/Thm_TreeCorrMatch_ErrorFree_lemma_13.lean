-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_13
-- name    : TreeCorrMatch.ErrorFree.lemma_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:26:04.400971+00:00
-- url     : https://prove2.me/theorems/4f5f52d8-c8cb-4b83-81dc-32fbd754ec19
-- title:
--   Lemma 13 — in ER$(n,\lambda/n)$ every depth-$d$ ball has fewer than $8e^2\lambda^d\log n$ nodes, except with probability $\tilde O(n^{-1/3})$
-- statement:
--   Let $G\sim\mathrm{ER}(n,\lambda/n)$ with $\lambda_n\to\infty$ and $\lambda_n\le(\log n)^K$ for some $K$, and let $\gamma\in(0,1)$. For a positive integer $d\le(\log n)^\gamma$ and a node $i$, let $N(i,d)$ be the set of nodes within distance $d$ from $i$ in $G$. Then
--
--   $$\mathbb P\big(\exists i\in[n]: |N(i,d)|\ge 8e^2\lambda^d\log n\big)=\tilde O(n^{-1/3}),$$
--
--   that is, there are constants $C$ and $K'$ such that for all large $n$ and every positive integer $d\le(\log n)^\gamma$ the probability is at most $C(\log n)^{K'}n^{-1/3}$.
--
--   The bound controls the size of all local trees at once, which makes the union bound over local-tree pairs in Lemma 6 possible.
--
--   Differences from the source:
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: Õ(n^{-1/3}) → ∃ C, K, for all large n: probability ≤ C (log n)^K n^{-1/3}; reason: Õ suppresses a polylogarithmic factor
--   - reading: d a positive integer with d ≤ (log n)^γ → the constants are fixed first and the bound holds for every such d (uniformly); reason: the paper's d is any integer in this range; its proof gives a bound uniform in d
--   - encoding: ER(n, λ/n) → the published Erdős–Rényi law RGGDetect.erLaw n (λ_n / n); reason: same object: each pair independently an edge with probability λ_n/n
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), pp. 39–40, Lemma 13 (PDF pp. 41–42)

import Mathlib
import Definitions.Def_RGGDetect_erLaw
import Definitions.Def_TreeCorrMatch_ErrorFree_LocalTree

open Filter Topology MeasureTheory

namespace TreeCorrMatch.ErrorFree

theorem lemma_13 (lam : ℕ → ℝ) (hlam : Tendsto lam atTop atTop)
    (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ Real.log n ^ γ →
      (RGGDetect.erLaw n (lam n / n)
          {G | ∃ i : Fin n, 8 * Real.exp 2 * lam n ^ d * Real.log n ≤ ((ball G i d).ncard : ℝ)}).toReal ≤
        C * Real.log n ^ K * (n : ℝ) ^ (-(1 : ℝ) / 3) := by sorry

end TreeCorrMatch.ErrorFree
