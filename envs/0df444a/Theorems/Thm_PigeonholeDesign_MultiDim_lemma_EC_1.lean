-- Prove2me | Theorems.Thm_PigeonholeDesign_MultiDim_lemma_EC_1
-- name    : PigeonholeDesign.MultiDim.lemma_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:18.237845+00:00
-- url     : https://prove2.me/theorems/5b86b6b0-3b7d-4d8e-bbd6-54eba6b788e7
-- title:
--   Lemma EC.1 — Hoeffding: P(|H(n) − αn| ≤ √(n log n)) ≥ 1 − 2/n²
-- statement:
--   Let $H(n)$ be a binomial random variable with $n\ge1$ trials and success probability $\alpha\in[0,1]$. Then
--   $$\Pr\Big(\big|H(n)-\alpha n\big|\le\sqrt{n\log n}\Big)\ \ge\ 1-\frac{2}{n^2}.$$
--
--   This is the form of Hoeffding's inequality the paper uses to control the imbalance between unmatched control and treated subjects, and the number of control subjects per sub-cube in the proof of Lemma 5.
--
--   **Formalization Note** The binomial law is written out: the probability is $\sum_k \binom nk\alpha^k(1-\alpha)^{n-k}$ over the $k\in\{0,\dots,n\}$ with $|k-\alpha n|\le\sqrt{n\log n}$. $\log$ is the natural logarithm; the paper does not say, and the constant $2/n^2$ requires it. The success probability is called $\alpha$ here (the paper's $p$) to avoid a clash with the number of continuous covariates.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec3, Lemma EC.1

import Mathlib

namespace PigeonholeDesign.MultiDim

theorem lemma_EC_1 (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    1 - 2 / (n : ℝ) ^ 2 ≤
      ∑ k ∈ (Finset.range (n + 1)).filter
          (fun k : ℕ => |(k : ℝ) - α * n| ≤ Real.sqrt (n * Real.log n)),
        (n.choose k : ℝ) * α ^ k * (1 - α) ^ (n - k) := by sorry

end PigeonholeDesign.MultiDim
