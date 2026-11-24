-- Prove2me | Theorems.Thm_TaoFivePrimes_smoothedVonMangoldtSlabIdentity
-- name    : TaoFivePrimes.smoothedVonMangoldtSlabIdentity
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T20:37:42.450069+00:00
-- url     : https://prove2.me/theorems/64f26461-2b2a-442f-ac59-a3d90b0d145b
-- title:
--   Smoothed von Mangoldt identity for the centred Vaughan decomposition with transferred slabs
-- statement:
--   ## Smoothed von Mangoldt identity for the centred Vaughan decomposition with transferred slabs
--
--   Let $x,\alpha,U,V\in\mathbb R$ with $x>0$, $U,V\ge 0$, $UV\le x/4$ and $x\le UV^2$, and let $\eta_0$ and $e(\cdot)$ be as above. Let $D$ be the set of odd $d\le\lfloor UV\rfloor$, and for $d\in D$ write $K(d)=\sum_{w>\lfloor V\rfloor}(\log w)\eta_0(dw/x)e(\alpha dw)$ for the transferred log-weighted slab sum, so that $S_3'=\sum_{\lfloor U\rfloor<d\le\lfloor UV\rfloor}\tfrac12\mu(d)K(d)$.
--
--   The claim is the exact identity
--   $$\mathrm{EV}(x,\alpha,U,V)\;+\;S_3'(x,\alpha,U,V)\;+\;B_1(x,\alpha,U,V)\;+\;B_0(x,\alpha,U,V)\;=\;\sum_{n\le x}\Lambda(n)\,\eta_0\!\Bigl(\frac nx\Bigr)e(\alpha n),$$
--   where $\mathrm{EV}$ is the centred Vaughan Type I sum (`eta0VaughanTypeISum`), and
--   $$B_1=\sum_{n\le x}\bigl(\mu_{>\lfloor U\rfloor}*\log_{\le\lfloor V\rfloor}\bigr)(n)\,\eta_0\!\Bigl(\frac nx\Bigr)e(\alpha n),\qquad B_0=\sum_{n\le x}\bigl(f_{\lfloor U\rfloor,\lfloor V\rfloor}*\zeta\bigr)(n)\,\eta_0\!\Bigl(\frac nx\Bigr)e(\alpha n),$$
--   with $f_{U,V}$ the Vaughan Type I correction coefficient and $\zeta$ the constant-arithmetic-function $1$.
--
--   This is the exact smoothed form of the von Mangoldt decomposition underlying Tao's Lemma 4.11 absorption step (arXiv:1201.6656v4, §4): the four terms — the centred Type I sum, the transferred half-logarithmic slab, the low-$w$ Möbius–log block and the correction-coefficient block — reconstruct the smoothed von Mangoldt sum with no error term. In particular the transferred slab is not an independent error term but one of four cancelling pieces; this is precisely why the triangle-inequality route to the sharp transfer gap fails numerically while the sharp gap itself holds, and it exhibits the Möbius cancellation as a global identity between the smoothed $\Lambda$-sum and the Vaughan blocks.
--
--   __Formalization note.__ The identity is a sum-level consequence of the pointwise arithmetic-function identity $\text{VaughanTypeIPart}+\mu_{>\lfloor U\rfloor}\tfrac12\log_{>\lfloor V\rfloor}+\mu_{>\lfloor U\rfloor}\log_{\le\lfloor V\rfloor}+f_{U,V}\zeta=\Lambda$, which follows from $\Lambda=\mu*\log$. The slab form of the second term is supplied by the companion node `TaoFivePrimes.sum_vaughanTruncatedHalfLog_eq_typeISlabS3`.
-- source:
--   T. Tao, 'Every odd number greater than 1 is the sum of at most five primes', Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4, Lemma 4.11 and Section 5. Structural form of the absorption identity behind TaoFivePrimes nodes child1/child3 (62275301) and the sharp transfer gap 7a679c13.

import Definitions.Def_TaoFivePrimes_TypeISlabSums
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction Finset

theorem TaoFivePrimes.smoothedVonMangoldtSlabIdentity
    (x alpha U V : ℝ) (hx0 : 0 < x) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    TaoFivePrimes.eta0VaughanTypeISum x alpha U V + TaoFivePrimes.typeISlabS3 x alpha U V
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
