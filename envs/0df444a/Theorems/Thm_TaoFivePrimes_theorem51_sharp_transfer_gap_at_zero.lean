-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_sharp_transfer_gap_at_zero
-- name    : TaoFivePrimes.theorem51_sharp_transfer_gap_at_zero
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T20:56:45.485987+00:00
-- url     : https://prove2.me/theorems/e18c780f-e7ad-4039-80e2-aa56b6546993
-- title:
--   The sharp transfer gap at alpha = 0: the elementary positivity case
-- statement:
--   ## The sharp transfer gap at $\alpha = 0$: the elementary positivity case
--
--   Let $x,U,V\in\mathbb R$ with $U,V\ge 40$, $U,V<x$, $UV\le x/4$ and $x\le UV^2$. Let $D$ be the set of odd $d\le \lfloor UV\rfloor$, and for $d\in D$ let $S_1(d)$, $S_0(d)$, $K(d)$ be the Type I slab sums of `TaoFivePrimes_TypeISlabSums` (log-weighted full inner support, unweighted full inner support, and log-weighted transferred inner support $w>\lfloor V\rfloor$), with $S_3'$ the transferred Möbius-weighted block.
--
--   The claim is the $\alpha=0$ instance of the sharp scalar transfer gap:
--   $$\sum_{d\in D}\Bigl(\bigl\|1_{d\le\lfloor U\rfloor}\mu(d)\bigr\|\,\|S_1(d)\|+\|f_d\|\,\|S_0(d)\|\Bigr)+\|S_3'\|\;\le\;\sum_{d\in D}\bigl(\|S_1(d)\|+\log d\cdot\|S_0(d)\|\bigr),$$
--   where $\mu$ is the Möbius function and $f_d$ the Vaughan Type I correction coefficient (the convolution of $\mu$ cut at $\lfloor U\rfloor$ with the von Mangoldt function cut at $\lfloor V\rfloor$).
--
--   At $\alpha=0$ the exponential test function takes the nonnegative real values $4\max(0,\log 2-|\log(2n/x)|)$ on odd $n$ and $0$ on even $n$. Consequently every slab sum is a nonnegative real, $K(d)$ is a sub-sum of $S_1(d)$ over the transferred support, and the inequality reduces to three elementary facts: $|\mu(d)|\le 1$, $|f_d|\le\log d$, and the support inclusion $K\subseteq S_1$. This case is the numerically extremal one for the sharp transfer gap (ratios $\approx 0.62$ across all tested scales, maximised near $\alpha\equiv 0$), so it constitutes the base case of the only remaining obligation in the reduction of child3 `TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI` (node 62275301) to the sharp gap `TaoFivePrimes.theorem51_sharp_transfer_gap` (node 7a679c13). Note that the triangle-inequality relaxation $\tfrac12\sum_{d>U}\|K(d)\|$ in place of the signed norm $\|S_3'\|$ is *false* (it exceeds the right-hand side by a factor $\approx 1.5$ at $\alpha=1/4$); already at $\alpha=0$ the proof uses the signed sub-sum structure rather than the pure triangle relaxation.
--
--   __Formalization note.__ The proof is self-contained over the definition bundle `Definitions.Def_TaoFivePrimes_TypeISlabSums`; it uses positivity of $\eta_0$, the support inclusion `transferredInnerSupport ⊆ fullInnerSupport`, Mathlib's Möbius bound `|μ(d)| ≤ 1`, and a direct divisor-sum proof of the coefficient bound `|f_d| ≤ log d` from `ζ * Λ = log`.
-- source:
--   T. Tao, 'Every odd number greater than 1 is the sum of at most five primes', Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4. Special case of TaoFivePrimes node 7a679c13 (theorem51_sharp_transfer_gap); base case of the reduction of child3 node 62275301.

import Definitions.Def_TaoFivePrimes_TypeISlabSums
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction Finset

theorem TaoFivePrimes.theorem51_sharp_transfer_gap_at_zero
    (x U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
            ‖TaoFivePrimes.typeISlabS1 x 0 d‖
          + ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
              ‖TaoFivePrimes.typeISlabS0 x 0 d‖))
      + ‖TaoFivePrimes.typeISlabS3 x 0 U V‖
    ≤ ∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (‖TaoFivePrimes.typeISlabS1 x 0 d‖ + Real.log d * ‖TaoFivePrimes.typeISlabS0 x 0 d‖) := by sorry
