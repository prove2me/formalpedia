-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_vaughan_split_centred_assembly_repaired
-- name    : TaoFivePrimes.theorem51_vaughan_split_centred_assembly_repaired
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-23T05:36:28.163314+00:00
-- url     : https://prove2.me/theorems/b3cd7a7a-eec3-498e-8726-a29c64f977e0
-- title:
--   Repaired centred Vaughan assembly: decomposition identity and per-divisor aligned Type I envelope
-- statement:
--   # Repaired centred Vaughan assembly: decomposition identity and aligned Type I envelope
--
--   Let $x,\alpha,U,V\in\mathbb R$ with $U,V\ge 40$, $U,V<x$, $UV\le x/4$ and $x\le UV^2$, and write $T(n)=\eta_0(n/x)e(\alpha n)$. This node packages, in a single conjunction, the two proved statements that make up the repaired centred Vaughan assembly — the exact analogue of `TaoFivePrimes.theorem51_vaughan_split_centred_assembly` (`401c5a3a`) at the repaired Type I interface.
--
--   The first conjunct is the centred identity
--   $$\sum_{n\le x}\Lambda(n)e(\alpha n)\eta_0(n/x)\;=\;\mathrm{EV}(x,\alpha,U,V)\;+\;\sum_{d\ge1}\sum_{w\ge1}\mathbf 1_{U<d,\ V<w,\ d,w\ \mathrm{odd}}\ \mu(d)\,\Theta_V(w)\,e(\alpha dw)\,\eta_0(dw/x),$$
--   where $\mathrm{EV}$ is `eta0VaughanTypeISum` and $\Theta_V$ is `theorem51Centered V`; it isolates the centred bilinear remainder $C$. The second conjunct is the per-divisor aligned Type I envelope: there is $c$ with $\|c(d)\|\le 1$ on the odd $d\le\lfloor UV\rfloor$ such that
--   $$\|\mathrm{EV}\|\;\le\;\sum_{d\in D}\Bigl\|\,\bigl(\mathbf 1_{d\le\lfloor U\rfloor}S_1(d)+\mathbf 1_{d>\lfloor U\rfloor}K(d)\bigr)+c(d)\log d\cdot S_0(d)\Bigr\|,$$
--   with $S_0,S_1$ the unweighted and logarithmically weighted slabs over the full inner support of $d$ and $K$ the logarithmically weighted slab over its part with $w>V$.
--
--   Both conjuncts are already-proved mission nodes (`8556af74` and `8176dc13`); this node re-exports them as one statement so that the existing reduction `Sol_leaf_reduction2.lean` (submission `80350542`, SKETCH_ACCEPTED) can be replayed verbatim against the repaired interface, yielding the repaired Vaughan split `TaoFivePrimes.theorem51_vaughan_split_repaired` (`3a0afac6`).
-- source:
--   T. Tao, 'Every odd number greater than 1 is the sum of at most five primes', Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4. Repaired analogue of TaoFivePrimes theorem51_vaughan_split_centred_assembly (401c5a3a): the centred Vaughan identity together with the per-divisor aligned Type I envelope of node 8176dc13 (logarithmic weight restricted to w > V for d > floor(U), unweighted bucket unrestricted). Packaging node so that the accepted leaf reduction 80350542 can be replayed against the repaired interface.

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces

theorem TaoFivePrimes.theorem51_vaughan_split_centred_assembly_repaired
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha =
      TaoFivePrimes.eta0VaughanTypeISum x alpha U V +
      ∑' d : ℕ, ∑' w : ℕ,
        (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
          (ArithmeticFunction.moebius d : ℂ) * (TaoFivePrimes.theorem51Centered V w : ℂ) *
            TaoFivePrimes.expCircle (alpha * d * w) * (TaoFivePrimes.eta0 ((d : ℝ) * w / x) : ℂ)
        else 0)) ∧
    (∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.eta0VaughanTypeISum x alpha U V‖ ≤
        ∑ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖
          (if d ≤ ⌊U⌋₊
            then ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w))
            else ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.transferredInnerSupport x V d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w)))
          + c d * (Real.log d : ℂ) *
              (∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                TaoFivePrimes.eta0VaughanTest x alpha (d * w))‖) := by sorry
