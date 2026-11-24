-- Prove2me | Theorems.Thm_TaoFivePrimes_centredVaughan_smoothedMangoldt_identity
-- name    : TaoFivePrimes.centredVaughan_smoothedMangoldt_identity
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T20:37:53.314807+00:00
-- url     : https://prove2.me/theorems/11a8b681-9cd4-489d-8871-6407e5a740bf
-- title:
--   Exact smoothed von Mangoldt identity for the centred Vaughan decomposition
-- statement:
--   ## Exact smoothed von Mangoldt identity for the centred Vaughan decomposition
--
--   Let $x,\alpha,U,V\in\mathbb R$ be arbitrary (no size hypotheses), and let $\eta_0$ and $e(\cdot)$ be the trapezoidal test function and the exponential as above. The claim is the exact identity
--   $$\mathrm{EV}(x,\alpha,U,V)\;+\;\sum_{n\le x}\bigl(\mu_{>\lfloor U\rfloor}*\tfrac12\log_{>\lfloor V\rfloor}\bigr)(n)\,\eta_0\!\Bigl(\frac nx\Bigr)e(\alpha n)\;+\;\sum_{n\le x}\bigl(\mu_{>\lfloor U\rfloor}*\log_{\le\lfloor V\rfloor}\bigr)(n)\,\eta_0\!\Bigl(\frac nx\Bigr)e(\alpha n)\;+\;\sum_{n\le x}\bigl(f_{\lfloor U\rfloor,\lfloor V\rfloor}*\zeta\bigr)(n)\,\eta_0\!\Bigl(\frac nx\Bigr)e(\alpha n)\;=\;\sum_{n\le x}\Lambda(n)\,\eta_0\!\Bigl(\frac nx\Bigr)e(\alpha n),$$
--   where $\mathrm{EV}$ is the centred Vaughan Type I sum (`eta0VaughanTypeISum`) and $f_{U,V}$ is the Vaughan Type I correction coefficient.
--
--   The identity holds for every real $x,U,V$: it is the smoothed, global form of the classical Vaughan decomposition of the von Mangoldt function, centred so that the Type I sum carries the Möbius truncation $\mu_{\le\lfloor U\rfloor}\log$ minus the correction term $f_{U,V}\zeta$, and completed by the transferred Möbius half-logarithm and the low block. It shows that the centred Vaughan package is an exact decomposition of the smoothed $\Lambda$-sum rather than an approximation, and it is the algebraic input for the reduction of the Type I envelope comparison to a cancellation estimate (nodes child1/child3). No support hypotheses on $U,V$ are needed here because the identity is pointwise in the arithmetic functions.
--
--   __Formalization note.__ This is the sum-level form of the arithmetic-function identity $\text{VaughanTypeIPart}+\mu_{>\lfloor U\rfloor}\tfrac12\log_{>\lfloor V\rfloor}+\mu_{>\lfloor U\rfloor}\log_{\le\lfloor V\rfloor}+f_{U,V}\zeta=\Lambda$, obtained from $\Lambda=\mu*\log$ by splitting $\log=\log_{\le\lfloor V\rfloor}+\tfrac12\log_{>\lfloor V\rfloor}+\tfrac12\log_{>\lfloor V\rfloor}$.
-- source:
--   Standard Vaughan decomposition of the von Mangoldt function (Vaughan 1977); T. Tao, arXiv:1201.6656v4, Section 4. Centred form used by TaoFivePrimes nodes child1/child3.

import Definitions.Def_TaoFivePrimes_TypeISlabSums
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction Finset

theorem TaoFivePrimes.centredVaughan_smoothedMangoldt_identity
    (x alpha U V : ℝ) :
    TaoFivePrimes.eta0VaughanTypeISum x alpha U V
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
                * TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊) n : ℝ) : ℂ)
            * TaoFivePrimes.eta0VaughanTest x alpha n))
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
                * TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.log) n : ℝ) : ℂ)
            * TaoFivePrimes.eta0VaughanTest x alpha n))
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊)
                * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
            * TaoFivePrimes.eta0VaughanTest x alpha n))
      = ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha n) := by sorry
