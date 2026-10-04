-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeII_dyadic_representation
-- name    : TaoFivePrimes.theorem51_typeII_dyadic_representation
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T20:56:35.366978+00:00
-- url     : https://prove2.me/theorems/65017650-171e-462b-9f3b-bd6fa3dc5b51
-- title:
--   Tao Section 5: the dyadic representation of the Type II sum
-- statement:
--   **The dyadic representation of the Type II sum.** Let $U,V\ge40$ with $U,V<x$, $UV\le\frac x4$ and $UV^2\ge x$, and for $W>0$ let
--
--   $$G(W)=\Bigl|\sum_{\substack{d>U,\ w>V\\ d,w\text{ odd}}}\mu(d)\,g(w)\,\mathbf 1_{[x/2W,\,x/W]}(d)\,\mathbf 1_{[W/2,\,W]}(w)\,e(\alpha dw)\Bigr|$$
--
--   be the dyadic block of the bilinear sum, with $g(w)=\sum_{b\mid w,\,b>V}\Lambda(b)-\frac12\log w$ the centred divisor coefficient. Then $G$ vanishes off $[V,\frac xU]$, the function $W\mapsto\frac{G(W)}W$ is integrable on $(0,\infty)$, and
--
--   $$T_{II}(x,\alpha,U,V)\ \le\ 4\int_0^\infty G(W)\,\frac{dW}{W}.$$
--
--   This is the measure-theoretic half of the source's Type II estimate. The inequality comes from the dyadic integral representation of the cutoff,
--   $$\eta_0\Bigl(\frac{dw}{x}\Bigr)=4\int_0^\infty\mathbf 1_{[x/2W,\,x/W]}(d)\,\mathbf 1_{[W/2,\,W]}(w)\,\frac{dW}{W},$$
--   which is public and proved on the platform as `TaoFivePrimes.eta0_dyadic_integral`, together with an interchange of the double sum with the integral and the triangle inequality. The support statement is the observation that both dyadic blocks are nonempty only when $V\le W\le\frac xU$: the $w$-block forces $w\le W$ against $w>V$, and the $d$-block forces $d\le\frac xW$ against $d>U$.
--
--   **Formalization Note** The Type II sum and the centred coefficient are the platform definitions imported from `Def_TaoFivePrimes_Theorem51Sums`; the double sum is over all natural numbers and is finite because of the indicators. $G$ is written out explicitly rather than existentially, so that the pointwise large-sieve bound can be stated for the same function.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, the passage from T_II to the integral of its dyadic blocks

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open MeasureTheory

theorem TaoFivePrimes.theorem51_typeII_dyadic_representation
    (x alpha U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∀ W : ℝ, W ∉ Set.Icc V (x / U) → ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ = 0)
      ∧ MeasureTheory.IntegrableOn (fun W : ℝ => ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ / W) (Set.Ioi 0)
      ∧ TaoFivePrimes.theorem51TypeII x alpha U V
          ≤ 4 * ∫ W in Set.Ioi (0:ℝ), ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ / W := by sorry
