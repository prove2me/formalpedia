-- Prove2me | Theorems.Thm_PiIrrationality_mignotte_parameter_selection
-- name    : PiIrrationality.mignotte_parameter_selection
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T06:18:05.635385+00:00
-- url     : https://prove2.me/theorems/8d84b2eb-473a-4280-8e37-aef37daf052c
-- title:
--   Selecting Mignotte’s Hermite parameter from denominator growth
-- statement:
--   Put $N_n=\operatorname{lcm}(1,\ldots,n)$ and $c=\cot(\pi/24)$. For all sufficiently large positive natural numbers $q$, one can choose a natural number $n\ge40000$ for which
--
--   $$13n^3N_n^5\exp\left(-3n\log\frac{1+c^2}{4}\right)\le\frac1{64q^5},$$
--   $$25N_n^5 2^{6n}n^3<\frac{q^{15}}{32}.$$
--
--   This is the eventual parameter-choice consequence of Section II, equations (14)–(16), used in the exponent-20 part of Theorem 1. The threshold is existential rather than the explicit threshold in the paper. The constants and powers in the two bounds are retained. It separates the prime-number and growth estimates from the Hermite construction; it does not assume an irrationality estimate for π.
-- source:
--   M. Mignotte, Approximations rationnelles de π et quelques autres nombres, Mém. Soc. Math. France 37 (1974), pp. 123–125, Section II equations (9)–(16). https://www.numdam.org/item/MSMF_1974__37__121_0.pdf (doi:10.24033/msmf.139).

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Norm

theorem PiIrrationality.mignotte_parameter_selection :
    ∃ Q : ℕ, ∀ q : ℕ, 0 < q → Q ≤ q →
      ∃ n : ℕ, 40000 ≤ n ∧
      13 * (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5 * Real.exp (-3 * n * Real.log ((1 + (Real.cos (Real.pi / 24) / Real.sin (Real.pi / 24))^2) / 4)) ≤ (1 / (32 * (q : ℝ)^5)) / 2 ∧
      25 * (Nat.lcmUpto n : ℝ)^5 * (2 : ℝ)^(6*n) * (n : ℝ)^3 < (q : ℝ)^15 / 32 := by sorry
