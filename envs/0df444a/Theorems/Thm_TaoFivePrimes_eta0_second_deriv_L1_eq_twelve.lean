-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_second_deriv_L1_eq_twelve
-- name    : TaoFivePrimes.eta0_second_deriv_L1_eq_twelve
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:57:10.234737+00:00
-- url     : https://prove2.me/theorems/d6a5bf0c-95d6-426d-9ab5-306e10ad237f
-- title:
--   Classical second-derivative mass of eta0 is twelve
-- statement:
--   For Tao's logarithmic triangular cutoff $\eta_0$, the ordinary second derivative has the exact integrable mass
--
--   $$\int_{\mathbb R}|\eta_0''(t)|\,dt=12.$$
--
--   The derivative is the classical derivative, defined as zero at points where differentiability fails. Consequently this integral measures the absolutely continuous part of the distributional second derivative only. The separate jumps of $\eta_0'$ at $1/4,1/2,1$ contribute masses $16,16,4$, giving the distributional total variation $12+36=48$ used in Tao's estimates. This statement does not identify the classical integral with that distributional variation.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, cutoff definition (1.7) and equation (5.13), printed p.26. This is the absolutely continuous contribution in the distributional interpretation explicitly explained immediately after (5.13). https://arxiv.org/pdf/1201.6656

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta0_second_deriv_L1_eq_twelve :
    (∫ t : ℝ, |deriv (deriv TaoFivePrimes.eta0) t|) = 12 := by sorry
