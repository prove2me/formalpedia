-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_sharp_transfer_gap_half_integer
-- name    : TaoFivePrimes.theorem51_sharp_transfer_gap_half_integer
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-23T04:21:55.249399+00:00
-- url     : https://prove2.me/theorems/54fa225d-4d27-4f07-a88d-774eef006762
-- title:
--   The sharp transfer gap for 2*alpha integral: reduction to the real test locus
-- statement:
--   ## The sharp transfer gap on the lattice $2\alpha \in \mathbb{Z}$
--
--   Let $x,U,V\in\mathbb R$ with $U,V\ge 40$, $U,V<x$, $UV\le x/4$ and $x\le UV^2$, and let $k\in\mathbb Z$ with
--   $$\alpha = \frac{k}{2}.$$
--   Write $D$ for the odd $d\le \lfloor UV\rfloor$, and for $d\in D$ let $S_1(d)$, $S_0(d)$ be the log-weighted and unweighted Type I slab sums over the full inner support, and $S_3'$ the transferred Möbius-weighted block (all at the parameter $\alpha$).
--
--   The claim is the sharp scalar transfer gap at these special frequencies:
--   $$\sum_{d\in D}\Bigl(\bigl\|1_{d\le\lfloor U\rfloor}\mu(d)\bigr\|\,\|S_1(d)\|+\|f_d\|\,\|S_0(d)\|\Bigr)+\|S_3'\|\;\le\;\sum_{d\in D}\bigl(\|S_1(d)\|+\log d\cdot\|S_0(d)\|\bigr),$$
--   with $\mu$ the Möbius function and $f_d$ the Vaughan Type I correction coefficient.
--
--   For $\alpha = k/2$ the exponential test evaluates on every odd integer $n$ to $e(\alpha n) = (-1)^{kn} = (-1)^k$ (as $n$ is odd), a single sign independent of $n$. Hence each slab sum at $\alpha = k/2$ equals $(-1)^k$ times the corresponding slab sum at $\alpha=0$, and all norms are unchanged. The result therefore reduces to the previously established $\alpha=0$ case, where the test function is non-negative on the odd integers and the inequality follows from $|\mu(d)|\le 1$, the coefficient bound $|f_d|\le\log d$, and the inclusion of the transferred support in the full inner support. This covers the frequencies $\alpha\in\tfrac12\mathbb Z$, i.e. the complete locus where the test function is real on the odd integers; the remaining (genuinely oscillatory) frequencies are the open content of the general sharp transfer gap `TaoFivePrimes.theorem51_sharp_transfer_gap` (node 7a679c13), the last link between child3 `62275301` and the five-primes chain.
-- source:
--   T. Tao, 'Every odd number greater than 1 is the sum of at most five primes', Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4. Lattice case 2*alpha integral of TaoFivePrimes node 7a679c13 (theorem51_sharp_transfer_gap); extends the alpha=0 node to all alpha with 2*alpha integral.

import Definitions.Def_TaoFivePrimes_TypeISlabSums
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction Finset

theorem TaoFivePrimes.theorem51_sharp_transfer_gap_half_integer
    (x U V : ℝ) (k : ℤ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
            ‖TaoFivePrimes.typeISlabS1 x ((k : ℝ) / 2) d‖
          + ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
              ‖TaoFivePrimes.typeISlabS0 x ((k : ℝ) / 2) d‖))
      + ‖TaoFivePrimes.typeISlabS3 x ((k : ℝ) / 2) U V‖
    ≤ ∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (‖TaoFivePrimes.typeISlabS1 x ((k : ℝ) / 2) d‖ + Real.log d * ‖TaoFivePrimes.typeISlabS0 x ((k : ℝ) / 2) d‖) := by sorry
