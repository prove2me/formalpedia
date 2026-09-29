-- Prove2me | Theorems.Thm_TaoFivePrimes_typeII_log_integral
-- name    : TaoFivePrimes.typeII_log_integral
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:51:33.969245+00:00
-- url     : https://prove2.me/theorems/f025b79b-a501-4ac2-8675-3543bf70a59c
-- title:
--   Tao Section 5: the logarithmic integral of the Type II estimate
-- statement:
--   For reals $0<b\le c$,
--
--   $$4\int_b^c\frac{\log W}{W}\,dW\ =\ 2\,\log\frac cb\,\log(cb).$$
--
--   With $b=V$ and $c=x/U$ this is the integral that converts the pointwise bound on the dyadic Type II sums into the Type II estimate of the source's minor-arc theorem: the bilinear sum is written as $4\int_0^\infty F(W)\frac{dW}{W}$, the integrand is supported in $V\le W\le x/U$, and each of the resulting pieces carries a factor $\log W$. The right-hand side then reads
--   $$2\log\frac{x}{UV}\,\log\frac{Vx}{U},$$
--   which is the shape in which the source records it.
--
--   The identity is the fundamental theorem of calculus for the primitive $\tfrac12\log^2W$ of $\log W/W$, together with $\log^2c-\log^2b=(\log c-\log b)(\log c+\log b)=\log\frac cb\log(cb)$.
--
--   **Formalization Note** The source's display writes the integral as $4\int_{V\le W\le x/U}\frac{dW}{W}$, without the factor $\log W$; the stated value $2\log\frac{x}{UV}\log\frac{Vx}{U}$ is the value of the integral *with* that factor, which is the one the argument uses, and is what is proved here. The integral is the interval integral with respect to Lebesgue measure.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5 (Minor arcs), subsection "Estimation of the Type II sum", the display "4 int_{V <= W <= x/U} dW/W = 2 log(x/UV) log(Vx/U)"; the factor log W is restored, see the Formalization Note

import Mathlib

open MeasureTheory

theorem TaoFivePrimes.typeII_log_integral (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) :
    4 * (∫ W in b..c, Real.log W / W) = 2 * Real.log (c / b) * Real.log (c * b) := by sorry
