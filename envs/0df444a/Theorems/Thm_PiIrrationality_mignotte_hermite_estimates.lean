-- Prove2me | Theorems.Thm_PiIrrationality_mignotte_hermite_estimates
-- name    : PiIrrationality.mignotte_hermite_estimates
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-03T06:18:01.98966+00:00
-- url     : https://prove2.me/theorems/62ae48cd-6017-4300-8316-8b07546e297e
-- title:
--   Mignotte’s degree-five Hermite remainder and coefficient estimates
-- statement:
--   Put $N_n=\operatorname{lcm}(1,\ldots,n)$ and $c=\cot(\pi/24)$. For every integer $n\ge40000$, positive integer numerator $p$ and positive natural denominator $q$ with $p/q<63/20$, there are complex numbers $R,U,T$ such that
--
--   $$R-U=\frac{i}{2}(\pi-p/q)T,\quad |U|\ge\frac1{32q^5},$$
--   $$|R|\le13n^3N_n^5\exp\left(-3n\log\frac{1+c^2}{4}\right),\quad |T|\le25N_n^5 2^{6n}n^3.$$
--
--   These are the simultaneous estimates from Mignotte’s degree-five Hermite construction at $x=i$ and $y=ip/(2q)$, including the nonzero Gaussian-integer lower bound. This formulation preserves the uniform quantifier over the construction parameter $n$ and the near-approximation restriction. It isolates the analytic construction from the subsequent choice of $n$ depending on $q$.
-- source:
--   M. Mignotte, Approximations rationnelles de π et quelques autres nombres, Mém. Soc. Math. France 37 (1974), pp. 123–125, Section II equations (9)–(16). https://www.numdam.org/item/MSMF_1974__37__121_0.pdf (doi:10.24033/msmf.139).

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Norm

theorem PiIrrationality.mignotte_hermite_estimates (n : ℕ) (hn : 40000 ≤ n)
    (p : ℤ) (q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hnear : (p : ℝ) / q < 63 / 20) :
    ∃ R U T : ℂ,
      R - U = (((Real.pi - (p : ℝ) / q) / 2 : ℝ) : ℂ) * Complex.I * T ∧
      1 / (32 * (q : ℝ)^5) ≤ ‖U‖ ∧
      ‖R‖ ≤ 13 * (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5 * Real.exp (-3 * n * Real.log ((1 + (Real.cos (Real.pi / 24) / Real.sin (Real.pi / 24))^2) / 4)) ∧
      ‖T‖ ≤ 25 * (Nat.lcmUpto n : ℝ)^5 * (2 : ℝ)^(6*n) * (n : ℝ)^3 := by sorry
