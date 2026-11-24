-- Prove2me | Theorems.Thm_TaoFivePrimes_typeIExpansion_three_bilinear_sums
-- name    : TaoFivePrimes.typeIExpansion_three_bilinear_sums
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-21T09:20:00.472291+00:00
-- url     : https://prove2.me/theorems/14ab880e-e492-4fec-8a90-f708d29542cd
-- title:
--   The platform Type I sum expands into three bilinear sums
-- statement:
--   ## Expansion of the platform Type I sum into three bilinear sums
--
--   Let $x>0$ and $\alpha,U,V\in\mathbb R$. Write $S_I=\texttt{eta0VaughanTypeISum}(x,\alpha,U,V)$, the weighted sum over $n\le\lfloor x\rfloor$ of the Vaughan Type I arithmetic function $\texttt{vaughanTypeIPart}$ against the test function $\eta_0(n/x)e(\alpha n)\mathbf 1_{(n,2)=1}$. Since
--   $$\texttt{vaughanTypeIPart}=\mu_{\le\lfloor U\rfloor}*\log-\mu_{\le\lfloor U\rfloor}*\Lambda_{\le\lfloor V\rfloor}*\zeta+\mu_{>\lfloor U\rfloor}*(\tfrac12\log)_{>\lfloor V\rfloor},$$
--   summing the three Dirichlet convolutions against a finitely supported test function and splitting each product into its two factors via the divisor pairing gives
--   $$S_I=\sum_{d\le x}\sum_{m\le x}\mu_{\le\lfloor U\rfloor}(d)\log m\,T(dm)\;-\;\sum_{d\le x}\sum_{m\le x}(\mu_{\le\lfloor U\rfloor}*\Lambda_{\le\lfloor V\rfloor})(d)\,\zeta(m)\,T(dm)\;+\;\sum_{d\le x}\sum_{w\le x}\mu_{>\lfloor U\rfloor}(d)\,(\tfrac12\log)_{>\lfloor V\rfloor}(w)\,T(dw),$$
--   where $T(n)=\eta_0(n/x)e(\alpha n)\mathbf 1_{(n,2)=1}$ and all sums are over $1\le d,m,w\le\lfloor x\rfloor$ (the ranges may be taken to be $\lfloor x\rfloor+1$ since $T$ vanishes beyond $x$; terms at $0$ vanish).
--
--   The step is the reindexing that both halves of the centred Vaughan split need: the decomposition identity isolates these three bilinear forms, and the Type I envelope comparison is proved term by term on the outer index $d$. The proof is the Dirichlet-pairing lemma (a finite-support Finset reindexing along `divisorsAntidiagonal`) applied to the three products, together with the indicator that the test function vanishes for $n\ge\lfloor x\rfloor+1$.
-- source:
--   Terence Tao, arXiv:1201.6656v4, Section 4 (Vaughan's identity, Lemma 4.11) and Section 5 preceding (5.8): writing the Type I part as bilinear sums over the small divisor before applying the envelope estimates.

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius BigOperators
open ArithmeticFunction Finset

theorem TaoFivePrimes.typeIExpansion_three_bilinear_sums (x alpha U V : ℝ) (hx : 0 < x) :
    TaoFivePrimes.eta0VaughanTypeISum x alpha U V =
      (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
        ((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
          ((ArithmeticFunction.log m : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * m))
      - (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
        (((TaoFivePrimes.arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) *
            TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt) d : ℝ) : ℂ) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) m : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * m))
      + (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
        ((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d : ℝ) : ℂ) *
          ((TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊ w : ℝ) : ℂ) *
            TaoFivePrimes.eta0VaughanTest x alpha (d * w)) := by sorry
