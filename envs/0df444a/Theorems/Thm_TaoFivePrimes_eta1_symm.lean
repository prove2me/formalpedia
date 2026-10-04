-- Prove2me | Theorems.Thm_TaoFivePrimes_eta1_symm
-- name    : TaoFivePrimes.eta1_symm
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:11:16.839703+00:00
-- url     : https://prove2.me/theorems/cbbf2c28-f039-4a18-aa03-076e4dd6cab7
-- title:
--   Tao Section 8: the trapezoid $\eta_1$ is symmetric about $1/2$
-- statement:
--   Throughout, $\eta_1$ is the symmetric trapezoidal cutoff of Section 8 of the source,
--
--   $$\eta_1(t)\;=\;\bigl(1-10\,\operatorname{dist}(t,[0.2,0.8])\bigr)_{+},$$
--
--   which is supported in $[0.1,0.9]$, equals $1$ on $[0.2,0.8]$, and rises and falls linearly with slope $\pm10$ in between.
--
--   It is symmetric about $t=\tfrac12$: $$\eta_1(1-t)=\eta_1(t)\qquad\text{for all }t\in\mathbb R.$$
--
--   This symmetry is what allows the three-prime count of Section 8 to be written as a single Fourier integral with a real, symmetric weight.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 8, equation (8.1)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta1_symm (t : ℝ) : TaoFivePrimes.eta1 (1 - t) = TaoFivePrimes.eta1 t := by sorry
