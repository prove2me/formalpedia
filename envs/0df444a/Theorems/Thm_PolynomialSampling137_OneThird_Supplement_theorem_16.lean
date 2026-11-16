-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_theorem_16
-- name    : PolynomialSampling137.OneThird.Supplement.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:51:37.250205+00:00
-- url     : https://prove2.me/theorems/044ce9ec-d1b6-49f0-9f95-317cce684845
-- title:
--   Theorem 16 — Sparse target two-sided binomial bound, exact degree, exact d=0,1 optima, and all stated tails
-- statement:
--   For every affinely independent $T\subseteq\mathbb F_2^N$ of cardinality $2^k$, let $\pi_T$ be uniform on $T$. Its minimum exact polynomial sampling degree is $k$, and for every $d\ge0$,
--   $$\beta(k,d)\le\mathcal O_d(\pi_T)\le\min\{1,(2-2^{-k})\beta(k,d)\}.$$
--   The lower bound holds for every flat entropy-$k$ law without a support hypothesis. The exact suprema at degrees zero and one are $2^{-k}$ and $(k+1)2^{-k}$. For $0<\varepsilon<1/2$ and $d\le(1/2-\varepsilon)k$ the upper bound $\min\{1,(2-2^{-k})\beta(k,d)\}$ is at most $2\exp(-2\varepsilon^2k)$. Along every sequence with $k\to\infty$, $g\to\infty$ and eventually $d\le k/2-g\sqrt k$, this upper bound (hence the overlap with every such $\pi_T$) tends to zero. The point-mass case $k=0$ is included. This companion result gives the sparse-target degree threshold on every affinely independent support.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
--   - encoding: the upper bound tends to zero whenever d ≤ k/2 − g(k)√k with g(k) → ∞ → the upper bound min{1,(2−2^(−k))β(k,d)} tends to zero along every sequence (k_j, d_j, g_j) with k_j → ∞, g_j → ∞ and eventually d_j ≤ k_j/2 − g_j√k_j; reason: sequential form of the source's limit; taking g_j = g(k_j) recovers it, and the overlap statement follows from the two-sided bound
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Theorem 16, printed p. 21; PDF p. 23

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem theorem_16 :
    (∀ (N k : ℕ) (T : Finset (Word N)), T.card = 2 ^ k →
      AffinelyIndependent (↑T : Set (Word N)) →
      MinimumDegree k (UniformOn T) ∧
      (∀ d : ℕ, BinomialTail k d ≤ BestOverlap d (UniformOn T) ∧
        BestOverlap d (UniformOn T) ≤ min 1
          ((2 - (2 : ℝ) ^ (-(k : ℤ))) * BinomialTail k d)) ∧
      BestOverlap 0 (UniformOn T) = (2 : ℝ) ^ (-(k : ℤ)) ∧
      BestOverlap 1 (UniformOn T) = (k + 1 : ℝ) * (2 : ℝ) ^ (-(k : ℤ)) ∧
      (∀ (ε : ℝ) (d : ℕ), 0 < ε → ε < 1/2 →
        (d : ℝ) ≤ (1/2 - ε) * k →
        min 1 ((2 - (2 : ℝ) ^ (-(k : ℤ))) * BinomialTail k d) ≤
          2 * Real.exp (-2 * ε ^ 2 * k))) ∧
    (∀ (N k d : ℕ) (π : Word N → ℝ), Flat k π →
      BinomialTail k d ≤ BestOverlap d π) ∧
    (∀ (k d : ℕ → ℕ) (g : ℕ → ℝ),
      Filter.Tendsto k Filter.atTop Filter.atTop →
      Filter.Tendsto g Filter.atTop Filter.atTop →
      (∀ᶠ j in Filter.atTop, (d j : ℝ) ≤ (k j : ℝ)/2 - g j * Real.sqrt (k j)) →
      Filter.Tendsto
        (fun j => min 1 ((2 - (2 : ℝ) ^ (-(k j : ℤ))) * BinomialTail (k j) (d j)))
        Filter.atTop (nhds 0)) := by sorry

end PolynomialSampling137.OneThird.Supplement
