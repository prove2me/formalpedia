-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_vaughan_split_repaired
-- name    : TaoFivePrimes.theorem51_vaughan_split_repaired
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-23T05:32:00.757092+00:00
-- url     : https://prove2.me/theorems/3a0afac6-ac36-4392-b58d-cf30f0f6f2d8
-- title:
--   Repaired Vaughan split: centred identity plus the per-divisor aligned Type I envelope
-- statement:
--   # Repaired Vaughan split: centred identity plus the per-divisor aligned Type I envelope
--
--   Let $x,\alpha,U,V\in\mathbb R$ with $U,V\ge 40$, $U,V<x$, $UV\le x/4$ and $x\le UV^2$, and let $T(n)=\eta_0(n/x)e(\alpha n)$. This node is the *repaired analogue* of the leaf `TaoFivePrimes.theorem51_vaughan_split` (`197dea21`): the same centred Vaughan split, but with the Type I envelope replaced by the per-divisor aligned envelope that is provable divisor-by-divisor (node `8176dc13`, `TaoFivePrimes.theorem51_child3_restricted_log_repair`).
--
--   With $D$ the odd $d\le\lfloor UV\rfloor$, $F(d)$ the full inner support (`fullInnerSupport x d`), $G(d)$ its part with $w>V$ (`transferredInnerSupport x V d`), $S_1(d)=\sum_{w\in F(d)}\log w\,T(dw)$, $S_0(d)=\sum_{w\in F(d)}T(dw)$ and $K(d)=\sum_{w\in G(d)}\log w\,T(dw)$ the conclusion is: there is $c:D\to\mathbb C$ with $\|c(d)\|\le 1$ and
--   $$\Bigl\|\sum_{n\le x}\Lambda(n)e(\alpha n)\eta_0(n/x)\Bigr\|\;\le\;\sum_{d\in D}\Bigl\|\,\bigl(\mathbf 1_{d\le\lfloor U\rfloor}S_1(d)+\mathbf 1_{d>\lfloor U\rfloor}K(d)\bigr)+c(d)\log d\cdot S_0(d)\Bigr\|\;+\;T_{\mathrm{II}}(x,\alpha,U,V).$$
--
--   Equivalently, $\|S\|\le T_{\mathrm I}^{\mathrm{rep}}(c)+T_{\mathrm{II}}$ for some admissible aligned $c$: the centred main term $\mathrm{EV}$ of the Vaughan decomposition is bounded by the repaired Type I envelope, while the centred bilinear remainder is exactly `theorem51TypeII` (the two terms being separated by the triangle inequality). Only the logarithmic weight is restricted to $w>V$ for $d>\lfloor U\rfloor$; the unweighted bucket $S_0(d)$ stays unrestricted.
--
--   The proof chains two already-proved statements by a triangle inequality: the centred identity $S=\mathrm{EV}+C$ (node `8556af74`) and the repaired child3 envelope for $\mathrm{EV}$ (node `8176dc13`), the latter witnessed by an explicit unimodular alignment factor. This yields a drop-in replacement for `197dea21` at the repaired interface; the extra $T_{\mathrm{II}}$ term is the same one appearing in the literal split, so downstream estimates involving the bilinear remainder are unaffected.
-- source:
--   T. Tao, 'Every odd number greater than 1 is the sum of at most five primes', Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4. Repaired analogue of TaoFivePrimes theorem51_vaughan_split (197dea21): the centred identity S = EV + C composed with the per-divisor aligned Type I envelope (node 8176dc13), in which the logarithmic weight is restricted to w > V for d > floor(U) and the unweighted bucket stays unrestricted. Separates the centred main term from the bilinear remainder T_II by the triangle inequality.

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces
open scoped BigOperators

theorem TaoFivePrimes.theorem51_vaughan_split_repaired
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ, (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
        (∑ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖
          (if d ≤ ⌊U⌋₊
            then ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w))
            else ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.transferredInnerSupport x V d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w)))
          + c d * (Real.log d : ℂ) *
              (∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                TaoFivePrimes.eta0VaughanTest x alpha (d * w))‖)
        + TaoFivePrimes.theorem51TypeII x alpha U V := by sorry
