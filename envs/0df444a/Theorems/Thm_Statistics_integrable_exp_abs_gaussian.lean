-- Prove2me | Theorems.Thm_Statistics_integrable_exp_abs_gaussian
-- name    : Statistics.integrable_exp_abs_gaussian
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:32:21.245613+00:00
-- url     : https://prove2.me/theorems/369f49b8-fb1e-4fd6-87fe-cc0712156fdf
-- title:
--   A Gaussian has all exponential moments of $|x|$
-- statement:
--   **A Gaussian has exponential moments of the absolute value.** For every $c \in \mathbb{R}$, $m \in \mathbb{R}$ and $v \ge 0$,
--   $$\int_{\mathbb{R}} e^{c|x|}\,\mathrm{d}\mathcal{N}(m,v)(x) < \infty .$$
--   This follows from the finiteness of the moment generating function $\mathbb{E}[e^{tX}] = \exp(tm + t^2 v/2)$ together with $e^{c|x|} \le e^{|c|x} + e^{-|c|x}$. The degenerate case $v = 0$, where the law is a Dirac mass, is included. Such a bound is exactly what is needed to dominate a Gaussian likelihood ratio and its derivative uniformly over a parameter neighbourhood, and hence to justify differentiating under the integral sign in a Gaussian model.
-- source:
--   Standard; the moment generating function of the normal law, E. L. Lehmann and G. Casella, Theory of Point Estimation, 2nd ed., Springer, 1998, Section 1.4; see also V. V. Buldygin and Yu. V. Kozachenko, Metric Characterization of Random Variables and Random Processes, AMS, 2000, Chapter 1 (sub-Gaussian variables).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem Statistics.integrable_exp_abs_gaussian (c m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => rexp (c * |x|)) (gaussianReal m v) := by sorry
