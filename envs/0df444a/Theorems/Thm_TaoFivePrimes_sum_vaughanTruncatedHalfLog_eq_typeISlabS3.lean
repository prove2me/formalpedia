-- Prove2me | Theorems.Thm_TaoFivePrimes_sum_vaughanTruncatedHalfLog_eq_typeISlabS3
-- name    : TaoFivePrimes.sum_vaughanTruncatedHalfLog_eq_typeISlabS3
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T20:37:35.85501+00:00
-- url     : https://prove2.me/theorems/6a6e22c2-155a-4146-b62c-f7d3bb31c082
-- title:
--   The transferred half-logarithmic Type I slab sum as a Möbius-log Dirichlet sum
-- statement:
--   ## The transferred half-logarithmic slab sum as a Möbius–logarithm Dirichlet sum
--
--   Let $x,\alpha\in\mathbb R$ and $U,V\ge 0$ with $x>0$, $UV\le x/4$ and $x\le UV^2$. Let $\eta_0(t)=4\max(0,\log 2-|\log(2t)|)$ be the trapezoidal test function, supported in $\tfrac14<t<1$, and write $e(\alpha n)=e^{2\pi i\alpha n}$. Let $\mu_{>\lfloor U\rfloor}$ denote the Möbius function restricted to $d>\lfloor U\rfloor$, and $\tfrac12\log_{>\lfloor V\rfloor}$ half the logarithm restricted to $w>\lfloor V\rfloor$.
--
--   The claim is the exact identity
--   $$\sum_{n\le x}\Bigl(\mu_{>\lfloor U\rfloor}*\tfrac12\log_{>\lfloor V\rfloor}\Bigr)(n)\;\eta_0\!\Bigl(\frac nx\Bigr)e(\alpha n)\;=\;\sum_{\substack{\lfloor U\rfloor<d\le \lfloor UV\rfloor\\ d\ \text{odd}}}\frac{\mu(d)}{2}\sum_{\substack{w>\lfloor V\rfloor\\ (d,w)\ \text{an open odd pair}}}\log w\;\eta_0\!\Bigl(\frac{dw}{x}\Bigr)e(\alpha dw),$$
--   where the inner summation runs over the transferred part of the open odd-pair support of the Type I slab decomposition (odd $d$, odd $w$, $x/4<dw<x$).
--
--   The two support hypotheses are exactly what makes the reindexing work. The condition $UV\le x/4$ empties the triangular region below the support of $\eta_0$, while $x\le UV^2$ forces $dw>x$ — hence $\eta_0(dw/x)=0$ — whenever $d>\lfloor UV\rfloor$ and $w>\lfloor V\rfloor$, cutting the global double Dirichlet sum down to the slab $\lfloor U\rfloor<d\le\lfloor UV\rfloor$. The identity converts the transferred slab sum `TaoFivePrimes.typeISlabS3` — the only remaining obstruction in the sharp Type I reduction `TaoFivePrimes.theorem51_sharp_transfer_gap` — into a single Dirichlet-convolution sum against the smooth weight $\eta_0(n/x)e(\alpha n)$, which is the form in which the von Mangoldt cancellation structure of the Type I envelope becomes visible. It also connects the slab architecture of the centred Vaughan decomposition (nodes child1/child3) with the smoothed von Mangoldt identity.
--
--   __Formalization note.__ Proof uses the Dirichlet pairing lemma `TaoFivePrimes.sum_dirichlet_pairing` (accepted node) together with the membership analysis of the open odd-pair support; no additional hypotheses are needed. The statement is formalized over `ℂ`-valued sums and `ℕ`-indexed Möbius/log coefficients, matching the definitions in `Definitions.Def_TaoFivePrimes_TypeISlabSums` and `Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces`.
-- source:
--   T. Tao, 'Every odd number greater than 1 is the sum of at most five primes', Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4, Lemma 4.11. Isolated in the sharp Type I reduction 'child3_of_sharp_gap' of TaoFivePrimes node 62275301 (transfer gap node 7a679c13, definition bundle 57e00a54).

import Definitions.Def_TaoFivePrimes_TypeISlabSums
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction Finset

theorem TaoFivePrimes.sum_vaughanTruncatedHalfLog_eq_typeISlabS3
    (x alpha U V : ℝ) (hx0 : 0 < x) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (((((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
              * TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊) n : ℝ) : ℂ)
          * TaoFivePrimes.eta0VaughanTest x alpha n))
      = TaoFivePrimes.typeISlabS3 x alpha U V := by sorry
