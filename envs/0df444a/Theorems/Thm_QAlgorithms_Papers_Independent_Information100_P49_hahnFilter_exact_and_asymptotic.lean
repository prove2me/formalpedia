-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P49_hahnFilter_exact_and_asymptotic
-- name    : QAlgorithms.Papers.Independent.Information100.P49.hahnFilter_exact_and_asymptotic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:49:14.118036+00:00
-- url     : https://prove2.me/theorems/befa7d7a-e31a-4569-8ab6-29235cf656a2
-- title:
--   Exact and asymptotic bounds for the discrete Hahn filter
-- statement:
--   For integers $n\ge1$ and $0\le D<n$, use the real polynomial binomial coefficient $\binom{x}{l}=\prod_{i=0}^{l-1}(x-i)/l!$ and define
--   $$Q_j(x)=\sum_{l=0}^j(-1)^l\binom jl\binom{j+l}l\frac{\binom xl}{\binom nl},\quad w_j=\frac{(2j+1)(n!)^2}{(n-j)!(n+j+1)!},\quad Z_D=\frac{(n!)^2}{(n-D-1)!(n+D+1)!},\quad p_{n,D}(x)=\frac{\sum_{j=0}^D w_jQ_j(x)}{1-Z_D}.$$
--   Here the displayed $Q_j$ and $w_j$ are used only for $j\le n$. Then $0<Z_D<1$ and
--   $$\sum_{j=0}^D w_j=1-Z_D,\qquad p_{n,D}(0)=1,\qquad \sum_{x=1}^n|p_{n,D}(x)|^2=\frac{Z_D}{1-Z_D},\qquad \max_{1\le x\le n}|p_{n,D}(x)|\le\sqrt{\frac{Z_D}{1-Z_D}}.$$
--   For fixed $0<t<1$, put $D_n=\lfloor tn\rfloor$ and
--   $$r_0(t)=\tfrac12\big[(1+t)\ln(1+t)+(1-t)\ln(1-t)\big]>0.$$
--   For every $\delta>0$, all sufficiently large $n$ satisfy $|p_{n,D_n}(x)|\le\exp(n[-r_0(t)+\delta])$ simultaneously for every integer $1\le x\le n$. Furthermore, for all sufficiently large $n$, $|p_{n,D_n}(x)|\le1$ on the whole integer grid $0\le x\le n$, and its Newton coefficients
--   $$a_s=\sum_{i=0}^s(-1)^{s-i}\binom si p_{n,D_n}(i)$$
--   satisfy $|a_s|\le2^s$ for $0\le s\le D_n$.
--
--   This gives an explicit polynomial approximation to the indicator of zero on the grid, with error decreasing exponentially in $n$.
--
--   **Formalization Note** The asymptotic exponential bound is the epsilon formulation of the source's logarithmic limsup bound; it also covers zero error without evaluating $\ln0$.
-- source:
--   Classical Capacity of Single-Mode Bosonic Gaussian Channels, arXiv:2610.22308v1, PDF p. 19, Eqs. (H37)–(H39)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49

namespace QAlgorithms.Papers.Independent.Information100.P49

open scoped BigOperators

/-- Eqs. (H37)–(H39), PDF p.19: exact normalization, squared grid error and
exponential approximation of the constructed polynomial, including the Newton bound.
The asymptotic error is expressed by its equivalent epsilon form, avoiding `log 0`. -/
theorem hahnFilter_exact_and_asymptotic :
    (∀ n D : ℕ, 1 ≤ n → D < n →
      0 < hahnRatio n D ∧ hahnRatio n D < 1 ∧
      (∑ j ∈ Finset.range (D + 1), hahnWeight n j) = 1 - hahnRatio n D ∧
      hahnFilter n D 0 = 1 ∧
      (∑ x ∈ Finset.Icc 1 n, |hahnFilter n D (x : ℝ)| ^ 2) =
        hahnRatio n D / (1 - hahnRatio n D) ∧
      (∀ x : ℕ, 1 ≤ x → x ≤ n →
        |hahnFilter n D (x : ℝ)| ≤
          Real.sqrt (hahnRatio n D / (1 - hahnRatio n D)))) ∧
    (∀ t : ℝ, 0 < t → t < 1 →
      0 < hahnRate t ∧
      (∀ delta : ℝ, 0 < delta → ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
        ∀ x : ℕ, 1 ≤ x → x ≤ n →
          |hahnFilter n ⌊t * (n : ℝ)⌋₊ (x : ℝ)| ≤
            Real.exp ((n : ℝ) * (-hahnRate t + delta))) ∧
      (∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
        (∀ x : ℕ, x ≤ n → |hahnFilter n ⌊t * (n : ℝ)⌋₊ (x : ℝ)| ≤ 1) ∧
        (∀ s : ℕ, s ≤ ⌊t * (n : ℝ)⌋₊ →
          |newtonCoefficient (hahnFilter n ⌊t * (n : ℝ)⌋₊) s| ≤ (2 : ℝ) ^ s))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P49
