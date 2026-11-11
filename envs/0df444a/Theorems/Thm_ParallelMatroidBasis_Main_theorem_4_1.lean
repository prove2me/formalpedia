-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_theorem_4_1
-- name    : ParallelMatroidBasis.Main.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:44.843776+00:00
-- url     : https://prove2.me/theorems/c2d909e0-c2e9-467f-ba32-a3533b6d4d30
-- title:
--   Theorem 4.1 — density preservation: $\Pr_S[|F\cap\binom Si|/\binom mi\ge p/2]\ge\frac14 2^{-2\frac{n-m}{n-i}\log(1/p)}$
-- statement:
--   Let $n,m,i$ be integers with $0\le i<n$ and $i\le m\le n$. Let $\mathcal F$ be a nonempty family of $i$-element subsets of $[n]$ and put
--   $$p=\frac{|\mathcal F|}{\binom ni}.$$
--   Let $S$ be a uniformly random $m$-element subset of $[n]$. Then
--   $$\Pr_S\left[\frac{\big|\mathcal F\cap\binom Si\big|}{\binom mi}\ \ge\ \frac p2\right]\ \ge\ \frac14\cdot 2^{-2\,\frac{n-m}{n-i}\,\log_2(1/p)} .$$
--
--   A dense family of $i$-sets keeps at least half of its relative density inside a random $m$-subset with probability bounded below in terms of $(n-m)/(n-i)$ and $\log(1/p)$. When $m=\lceil n(1-1/\log n)\rceil$, $i\le n/2$ and $p\ge n^{-O(1)}$ the bound is a constant; Lemma 6.5 applies it to the family of independent sets spanning a fixed element.
--
--   **Formalization Note.** $[n]$ is `Fin n`; the probability over $S$ is the fraction of the $m$-subsets of `Fin n` in the event.
--
--   Differences from the source:
--   - encoding: Pr over a uniformly random m-element set S ⊆ [n] → the number of m-subsets of Fin n in the event divided by (n choose m); reason: the uniform probability on a finite set is the fraction of its elements in the event
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Theorem 4.1, p.14 (PDF p.16)

import Mathlib

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-- Theorem 4.1 (density preservation under subsampling), PDF p.16 (printed p.14). Let
`0 ≤ i < n` and `i ≤ m ≤ n`, let `∅ ≠ F ⊆ ([n] choose i)` and `p = |F| / (n choose i)`. For a
uniformly random `m`-element set `S ⊆ [n]`,
`Pr_S[|F ∩ (S choose i)| / (m choose i) ≥ p/2] ≥ (1/4) · 2^{−2 ((n−m)/(n−i)) log₂(1/p)}`. -/
theorem theorem_4_1 (n m i : ℕ) (hin : i < n) (him : i ≤ m) (hmn : m ≤ n)
    (F : Finset (Finset (Fin n))) (hF : F.Nonempty)
    (hFi : F ⊆ (Finset.univ : Finset (Fin n)).powersetCard i) :
    let p : ℝ := (F.card : ℝ) / (n.choose i : ℝ)
    (1 / 4 : ℝ) * (2 : ℝ) ^ (-2 * (((n : ℝ) - m) / ((n : ℝ) - i)) * Real.logb 2 (1 / p)) ≤
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
          (fun S => p / 2 ≤ ((F ∩ S.powersetCard i).card : ℝ) / (m.choose i : ℝ))).card : ℝ) /
        (n.choose m : ℝ) := by sorry

end ParallelMatroidBasis.Main
