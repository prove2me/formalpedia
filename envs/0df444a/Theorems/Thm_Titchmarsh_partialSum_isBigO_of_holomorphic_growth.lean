-- Prove2me | Theorems.Thm_Titchmarsh_partialSum_isBigO_of_holomorphic_growth
-- name    : Titchmarsh.partialSum_isBigO_of_holomorphic_growth
-- status  : Proved
-- author  : @lll
-- created : 2026-11-20T23:12:57.5187+00:00
-- url     : https://prove2.me/theorems/0cfc5f9d-8e47-4920-b235-f80b5f4f55a7
-- title:
--   Partial sums $O(N^{\sigma_0+\varepsilon})$ from a slowly growing holomorphic continuation
-- statement:
--   Let $a:\mathbb N\to\mathbb C$ be a sequence with $|a(n)|\le1$ for all $n$, and let $\sigma_0\ge0$. Suppose the Dirichlet series $\sum_{n\ge1}a(n)n^{-s}$, which converges absolutely for $\operatorname{Re}s>1$, extends to a function $F$ holomorphic on the half-plane $\operatorname{Re}s>\sigma_0$, and that $F$ grows slower than every power of $|t|$ to the right of $\sigma_0$:
--
--   1. $F$ is holomorphic on $\{s:\operatorname{Re}s>\sigma_0\}$;
--   2. $F(s)=\sum_{n\ge1}a(n)n^{-s}$ for $\operatorname{Re}s>1$;
--   3. for every $\delta>0$ and $\varepsilon>0$ there is $C$ with $|F(\sigma+it)|\le C|t|^{\varepsilon}$ whenever $\sigma_0+\delta\le\sigma\le2$ and $|t|\ge1$.
--
--   Then for every $\varepsilon>0$,
--
--   $$
--   \sum_{n=1}^{N}a(n)=O_\varepsilon\!\left(N^{\sigma_0+\varepsilon}\right)\qquad(N\to\infty).
--   $$
--
--   This is the contour argument in Titchmarsh–Heath-Brown's proof of Theorem 14.25(C), stated for a general Dirichlet series with bounded coefficients. There it is applied to $a=\mu$, $F=1/\zeta$, $\sigma_0=\tfrac12$, with hypothesis 3 supplied by (14.2.6) under RH. The general form applies equally to other bounded arithmetic functions, such as the Liouville function or twisted Möbius sums, whose Dirichlet series have a holomorphic continuation of moderate growth.
--
--   **Formalization Note.** Holomorphy is `DifferentiableOn ℂ`, and the Dirichlet series is Mathlib's `LSeries a`. The hypothesis $\sigma_0\ge0$ (any value works for $\sigma_0\ge1$, where the conclusion is trivial) ensures the shifted contour stays to the right of the pole of $x^w/w$ at $w=0$.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf, §14.25, proof of Theorem 14.25(C), equation (14.25.3), p. 370, using Perron's formula in the form of Lemma 3.12 (§3.12, pp. 60–61).

import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace Titchmarsh

theorem partialSum_isBigO_of_holomorphic_growth (a : ℕ → ℂ) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    (σ₀ : ℝ) (hσ₀ : 0 ≤ σ₀) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | σ₀ < s.re})
    (hFL : ∀ s : ℂ, 1 < s.re → F s = LSeries a s)
    (hgrowth : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
      σ₀ + δ ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖F s‖ ≤ C * |s.im| ^ ε) :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n)
        (fun N : ℕ => (N : ℝ) ^ (σ₀ + ε)) := by sorry

end Titchmarsh
