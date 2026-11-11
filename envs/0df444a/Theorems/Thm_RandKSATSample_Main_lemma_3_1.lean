-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_3_1
-- name    : RandKSATSample.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:00:09.202449+00:00
-- url     : https://prove2.me/theorems/d391b48c-3c37-40d1-985d-2b3f738a90e3
-- title:
--   Lemma 3.1 — expansion: with probability ≥ 1 − 2n0/n² − (4/3)4^{−n^{1/3}}, every set S of at most r clauses has |vbl(S)| ≥ (k−4)|S|
-- statement:
--   Let $k\ge30$ and $n^2\ge2n_0$, with $n_0=e^{k-3}\lambda(k-4)^4$, $\lambda=1+m/n$, $q_0=(4n_0)^{-1/3}$ and $r=\lfloor q_0n\rfloor$ as in (3.1). For a random formula $\Phi\sim\Phi(k,n,m)$ in the occurrence model,
--   $$\Pr\Big[\forall S\subseteq\mathcal C,\ |S|\le r:\ |\mathrm{vbl}(S)|\ge(k-4)|S|\Big]\ \ge\ 1-\frac{2n_0}{n^2}-\frac43\cdot4^{-n^{1/3}}.$$
--   This expansion of small clause sets is one of the three structural events (Lemmas 3.1–3.3) on which the high-degree core is analysed.
--
--   Differences from the source: none.
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 11, Lemma 3.1

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure

set_option autoImplicit false

namespace RandKSATSample.Main

/-- Lemma 3.1: for `k ≥ 30` and `n² ≥ 2 n0`, with probability at least
`1 − 2n0/n² − (4/3)·4^{−n^{1/3}}` every set `S` of at most `r` clauses has
`|vbl(S)| ≥ (k − 4)|S|`. -/
theorem lemma_3_1 (n m k : ℕ) (hk : 30 ≤ k) (hn : 2 * n0 n m k ≤ (n : ℝ) ^ 2) :
    1 - 2 * n0 n m k / (n : ℝ) ^ 2 - 4 / 3 * (4 : ℝ) ^ (-(n : ℝ) ^ ((1 : ℝ) / 3)) ≤
      probF n m k (fun Φ => Expansion Φ) := by sorry

end RandKSATSample.Main
