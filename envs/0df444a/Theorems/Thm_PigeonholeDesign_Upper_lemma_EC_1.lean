-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_lemma_EC_1
-- name    : PigeonholeDesign.Upper.lemma_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:28.130087+00:00
-- url     : https://prove2.me/theorems/0c0a8e80-1f8e-466e-98b3-5367886b59ad
-- title:
--   Lemma EC.1 — Hoeffding: P(|H(n) − pn| ≤ √(n log n)) ≥ 1 − 2/n² for a binomial H(n)
-- statement:
--   Let $n\ge1$ be an integer, $p\in[0,1]$, and let $H(n)$ be a binomial random variable with $n$ trials and success probability $p$, i.e. $P(H(n)=k)=\binom nk p^k(1-p)^{n-k}$ for $k=0,\dots,n$. Then
--   $$P\bigl(|H(n)-pn|\le\sqrt{n\log n}\bigr)\ \ge\ 1-\frac{2}{n^2}.$$
--
--   This is Hoeffding's inequality with deviation $\sqrt{n\log n}$. In the proof of Lemma 3 it controls the imbalance between the unmatched control and treated subjects, which is what makes the last $T-\tau$ balancing subjects few.
--
--   **Formalization Note** The probability is written as the sum of the binomial weights over the integers $k\in\{0,\dots,n\}$ with $|k-pn|\le\sqrt{n\log n}$. The logarithm is the natural one (`Real.log`); the paper does not specify the base, and the constant $2/n^2$ requires the natural logarithm. The hypothesis $n\ge1$ is implicit in the page (the bound $2/n^2$ is undefined at $n=0$).
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec3 (PDF p. 41), Lemma EC.1

import Mathlib

namespace PigeonholeDesign.Upper

theorem lemma_EC_1 (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - 2 / (n : ℝ) ^ 2 ≤
      ∑ k ∈ (Finset.range (n + 1)).filter
          (fun k : ℕ => |(k : ℝ) - p * n| ≤ Real.sqrt (n * Real.log n)),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by sorry

end PigeonholeDesign.Upper
