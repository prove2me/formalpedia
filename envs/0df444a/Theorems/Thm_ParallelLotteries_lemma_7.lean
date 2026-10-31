-- Prove2me | Theorems.Thm_ParallelLotteries_lemma_7
-- name    : ParallelLotteries.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:53.822761+00:00
-- url     : https://prove2.me/theorems/d988c42b-4ed4-4e7c-8baf-37284212a12c
-- title:
--   Lemma 7: $f(p_i,p_j)$ is decreasing in $p_i$ and increasing in $p_j$
-- statement:
--   Let $k\ge1$ and let $f(p_i,p_j)=\frac{p_j-1/k}{p_j-p_i}h(p_i)+\frac{1/k-p_i}{p_j-p_i}h(p_j)$ with $h(p)=pk/(1-(1-p)^k)$ and $h(0)=1$. On the region $0\le p_i<1/k<p_j\le1$:
--
--   1. for every fixed $p_j\in(1/k,1]$, $p_i\mapsto f(p_i,p_j)$ is strictly decreasing on $[0,1/k)$;
--   2. for every fixed $p_i\in[0,1/k)$, $p_j\mapsto f(p_i,p_j)$ is strictly increasing on $(1/k,1]$.
--
--   Hence $f$ is largest toward the corner $p_i\to0$, $p_j\to1$, where it tends to $2-1/k$.
--
--   Differences from the source:
--   - reading: $h(0)$, which (60) leaves as $0/0$ while the lemma includes $p_i=0$ → $h(0):=1$; reason: the limit of $h$ at $0^+$, the only value under which the lemma's case $p_i=0$ is meaningful
--   - reading: $1/k<p_j$ → $1/k<p_j\le1$; reason: $p_j$ is a win probability; for $p_j>1$, (60) can divide by zero ($p=2$, $k$ even)
--   - reading: "decreasing"/"increasing" → strictly (`StrictAntiOn`/`StrictMonoOn`); reason: the page's proof calls the numerator of (62) "positive"; the strict form implies the weak one, and it holds because $f$ is a chord of $h$ at $1/k$ and $h$ is strictly convex for $k\ge2$ (for $k=1$ the region is empty)
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, Lemma 7, p.34

import Mathlib
import Definitions.Def_ParallelLotteries_hf

namespace ParallelLotteries

/-- **Lemma 7 (monotonicity of f)** — Arnosti–Randolph, SSRN 3370605 (preprint), App. D.2, p.34:
"Lemma 7. For 0 ≤ p_i < 1/k < p_j, the function f defined in (59) is decreasing in p_i and
increasing in p_j."

For every `k ≥ 1`:
1. for every `p_j ∈ (1/k, 1]`, `p_i ↦ f(p_i, p_j)` is strictly decreasing on `[0, 1/k)`;
2. for every `p_i ∈ [0, 1/k)`, `p_j ↦ f(p_i, p_j)` is strictly increasing on `(1/k, 1]`.

**Formalization Note.** `h(0) := 1` (see `ParallelLotteries.hfun`). `p_j ≤ 1` because `p_j` is a
win probability. "Decreasing"/"increasing" are read in the strict sense (`StrictAntiOn`/
`StrictMonoOn`), which implies the weak one: the page's proof calls the numerator of (62) "positive",
and `f` is a chord of `h` evaluated at `1/k`, so the strict convexity of `h` for `k ≥ 2`
(`ParallelLotteries.lemma_8`) gives strictness. For `k = 1` the range `(1/k, 1]` is empty. -/
theorem lemma_7 (k : ℕ) (hk : 1 ≤ k) :
    (∀ pj : ℝ, 1 / (k : ℝ) < pj → pj ≤ 1 →
      StrictAntiOn (fun pi => fval k pi pj) (Set.Ico 0 (1 / (k : ℝ)))) ∧
    (∀ pi : ℝ, 0 ≤ pi → pi < 1 / (k : ℝ) →
      StrictMonoOn (fun pj => fval k pi pj) (Set.Ioc (1 / (k : ℝ)) 1)) := by sorry

end ParallelLotteries
