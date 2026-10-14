-- Prove2me | Theorems.Thm_PigeonholeDesign_Lower_lemma_EC_2
-- name    : PigeonholeDesign.Lower.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:19:09.257823+00:00
-- url     : https://prove2.me/theorems/09494891-442a-450b-8715-2fa571c47f60
-- title:
--   Lemma EC.2 — binomial mean absolute deviation: E|X − np| = √(2p(1−p)n/π) + O(n^{−1/2})
-- statement:
--   Let $X$ be a binomial random variable with $n$ trials and success probability $p\in[0,1]$, so that
--   $$\mathbb E\,|X-np| \;=\;\sum_{k=0}^{n}\binom nk p^k(1-p)^{n-k}\,|k-np| .$$
--   For each fixed $p$ there is a constant $C$ (depending on $p$) such that for all $n\ge1$
--   $$\Bigl|\ \mathbb E\,|X-np|-\sqrt{\frac{2p(1-p)}{\pi}\,n}\ \Bigr|\;\le\;\frac{C}{\sqrt n},$$
--   that is, $\mathbb E|X-np|=\sqrt{2p(1-p)n/\pi}+O(n^{-1/2})$ as $n\to\infty$.
--
--   This is the classical asymptotic of the binomial mean absolute deviation (Blyth 1980, equation (2.4)). In the proof of Lemma 4 it gives the per-pigeonhole lower bound: the number of left points of an alternating cell that land in control is binomial with success probability $1/2$.
--
--   **Formalization Note** The expectation is written out as the finite sum over the binomial law. The $O(n^{-1/2})$ is read with $p$ fixed: the constant $C$ is chosen after $p$ and before $n$. At $p\in\{0,1\}$ both sides vanish.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec3, Lemma EC.2 (citing Blyth 1980, eq. (2.4))

import Mathlib
import Definitions.Def_PigeonholeDesign_Lower_Setting

namespace PigeonholeDesign.Lower

theorem lemma_EC_2 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) * |(k : ℝ) - n * p|)
        - Real.sqrt (2 * p * (1 - p) / Real.pi * n)| ≤ C / Real.sqrt n := by sorry

end PigeonholeDesign.Lower
