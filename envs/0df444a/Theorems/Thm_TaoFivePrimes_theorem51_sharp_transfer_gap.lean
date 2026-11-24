-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_sharp_transfer_gap
-- name    : TaoFivePrimes.theorem51_sharp_transfer_gap
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-22T14:52:54.541821+00:00
-- url     : https://prove2.me/theorems/7a679c13-718c-40e2-8bec-19a2367ce736
-- title:
--   Sharp scalar transfer gap for the centred Vaughan Type I comparison (TaoFivePrimes child3)
-- statement:
--   ## The sharp scalar transfer gap for the centred Vaughan Type I comparison
--
--   Let $x,\alpha\in\mathbb R$ and $U,V\ge 40$ with $U,V<x$, $UV\le x/4$ and $x\le UV^2$. Let $D$ be the set of odd $d\le UV$ (`TaoFivePrimes.theorem51Divisors`). For $d\in D$ let $S_1(d)$, $S_0(d)$, $K(d)$ and $S_3'$ be the slab sums of the definition `TaoFivePrimes_TypeISlabSums` (see its description): $S_1$ is the log-weighted Type I slab sum over the full inner support, $S_0$ the unweighted one, $K$ the log-weighted sum over the transferred part $w>\lfloor V\rfloor$ of the support, and $S_3'=\sum_{\lfloor U\rfloor<d\le UV,\ d\in D}\tfrac12\mu(d)K(d)$ the transferred half-logarithmic block as a single global M\"obius-weighted sum. Finally let $f_d$ be the Vaughan Type I correction coefficient `vaughanTypeICorrectionCoefficient`.
--
--   The claim is the scalar inequality
--
--   $$\sum_{d\in D}\Bigl(|\mu_{\le U}(d)|\,\|S_1(d)\|+|f_d|\,\|S_0(d)\|\Bigr)+\|S_3'\|\;\le\;\sum_{d\in D}\Bigl(\|S_1(d)\|+\log d\,\|S_0(d)\|\Bigr).$$
--
--   This is exactly the remaining estimate in the proof of Tao's Lemma 4.11 absorption step (arXiv:1201.6656v4, §4), and it is the sole missing input for the Type I envelope comparison `TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI` (node 'child3'): the reduction `child3_of_sharp_gap` proves the comparison from this inequality. The crucial point is that $S_3'$ keeps the M\"obius cancellation: the triangle version $\tfrac12\sum_{d>U}\|K(d)\|\le\sum_{d>U}\|S_1(d)\|$, which is what the displayed proof of the source silently uses, is numerically false (ratio $1.24$ at $U=V=40$, $x=64000$, $\alpha=1/4$), while the global form above holds with margin $\ge 1.75\times$ on all tested data. After cancelling the common $\sum_d\|S_1(d)\|$ term (using $|\mu_{\le U}(d)|\le 1$ and the proved bound $|f_d|\le\log d$), the reduced core is the M\"obius cancellation estimate $\|\sum_{U<d\le UV}\tfrac12\mu(d)K(d)\|\le \sum_{d>U}\|S_1(d)\|+(\text{slack from non-squarefree }d\le U)$, i.e. a bilinear estimate for the windowed log-sums $K(d)=\sum_{w>V}(\log w)\,\eta_0(dw/x)e(\alpha dw)$. Proving this scalar gap completes child3 and, downstream, the centred Vaughan assembly.
-- source:
--   Terence Tao, 'Every odd number greater than 1 is the sum of at most five primes', Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4, Lemma 4.11 (the absorption of the half-logarithmic leftover into the Type I envelope, step (4.18)) and its Section 5 use. Isolated as the reduction 'child3_of_sharp_gap' of TaoFivePrimes node 62275301 (TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI).

import Definitions.Def_TaoFivePrimes_TypeISlabSums
open scoped BigOperators

theorem TaoFivePrimes.theorem51_sharp_transfer_gap
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
            ‖TaoFivePrimes.typeISlabS1 x alpha d‖
          + ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
              ‖TaoFivePrimes.typeISlabS0 x alpha d‖))
      + ‖TaoFivePrimes.typeISlabS3 x alpha U V‖
    ≤ ∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (‖TaoFivePrimes.typeISlabS1 x alpha d‖ + Real.log d * ‖TaoFivePrimes.typeISlabS0 x alpha d‖) := by sorry
