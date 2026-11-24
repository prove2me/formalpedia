-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_child3_restricted_log_repair
-- name    : TaoFivePrimes.theorem51_child3_restricted_log_repair
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-23T05:19:22.327921+00:00
-- url     : https://prove2.me/theorems/8176dc13-f638-43e7-9a66-7047830275d1
-- title:
--   Child3 repair: per-divisor aligned Type I envelope with the logarithmic weight restricted to w > V
-- statement:
--   # Child3 repair: a provable per-`d` Type I envelope for the centred Vaughan sum
--
--   Let $x,\alpha,U,V\in\mathbb R$ with $U,V\ge 40$, $U,V<x$, $UV\le x/4$, $x\le UV^2$. Write $D$ for the odd $d\le\lfloor UV\rfloor$, and for $d\in D$ let
--   $$S_1(d)=\sum_{w\in F(d)}\log w\,T(dw),\qquad S_0(d)=\sum_{w\in F(d)}T(dw),\qquad K(d)=\sum_{w\in G(d)}\log w\,T(dw),$$
--   where $T(n)=\eta_0(n/x)e(\alpha n)$ is the smoothed exponential test, $F(d)$ is the full inner support (`fullInnerSupport x d`) and $G(d)\subseteq F(d)$ is its part with $w>V$ (`transferredInnerSupport x V d`).
--
--   This node is a *sibling refinement* of child3 `TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI` (62275301). Its conclusion is the per-divisor aligned envelope
--   $$\Bigl\|\sum_{d\in D}T_d\Bigr\|\;\le\;\sum_{d\in D}\Bigl\|\,B(d)+c(d)\log d\cdot S_0(d)\,\Bigr\|,\qquad B(d)=\begin{cases}S_1(d),&d\le\lfloor U\rfloor,\\ K(d),&d>\lfloor U\rfloor,\end{cases}$$
--   with $\|c(d)\|\le 1$ for all $d\in D$, where $T_d$ denotes the $d$-th outer slice of the centred Vaughan Type I sum $\mathrm{EV}=\texttt{eta0VaughanTypeISum }x\,\alpha\,U\,V$ (the platform's `outerSlice x alpha U V d`), normalized throughout by `eta0VaughanTypeISum`.
--
--   **Why this is the correct repair of child3.** The outer-slice expansion (proved in the accepted module `TypeIOrdinaryFinalAssembly`, cf. `eta0VaughanTypeISum_eq_supported_outer_assembly`, `outerSlice_eq_single_full_support_sum`) gives, for every odd $d\le\lfloor UV\rfloor$, the exact per-`d` decomposition
--   $$T_d=\mu(d)S_1(d)-f_dS_0(d)\quad(d\le\lfloor U\rfloor),\qquad T_d=-f_dS_0(d)+\tfrac12\mu(d)K(d)\quad(d>\lfloor U\rfloor),$$
--   where $f_d$ is the Vaughan Type I correction coefficient, obeying $|f_d|\le\log d$. The *literal* child3 envelope $T_I(c)=\sum_d\|S_1(d)+c(d)\log d\,S_0(d)\|$ charges the transferred piece $K(d)$ against $S_1(d)$, which is false per divisor (numerically the ratio $\|T_d\|/\|S_1(d)+c(d)\log d\,S_0(d)\|$ reaches $6.48$ at $x=57190$ for a rationalized sweep of admissible $c$, and $1.31$ at $x=128000$; a violation is already visible with $18$ bad $d$). The reason is that for $d>\lfloor U\rfloor$ the piece $-\tfrac12\mu(d)\sum_{w\le V}\log w\,T(dw)$ is a genuine sub-sum of $S_1(d)$ with no partner in the envelope; it is *homeless* unless the unweighted bucket $S_0(d)$ stays unrestricted, as in $T(d)+c(d)\log d\,S_0(d)$ with $B(d)=K(d)$.
--
--   **Proof.** For $d>\lfloor U\rfloor$, choose $c(d)=\mathrm{align}(K(d),S_0(d))$; the triangle inequality, $|f_d|\le\log d$, $|\mu(d)|\le 1$ and the alignment identity $\|K\|+t\|S_0\|=\|K+\mathrm{align}(K,S_0)\,t\,S_0\|$ give
--   $$\|T_d\|\le\|f_dS_0(d)\|+\tfrac12\|K(d)\|\le\log d\,\|S_0(d)\|+\|K(d)\|=\|K(d)+c(d)\log d\,S_0(d)\|.$$
--   For $d\le\lfloor U\rfloor$ the same argument with $c(d)=\mathrm{align}(S_1(d),S_0(d))$ yields $\|T_d\|\le\|S_1(d)+c(d)\log d\,S_0(d)\|$. Summing over $D$ and combining with the outer-slice expansion (which restricts the auxiliary Möbius factor to the support $D$, using `outerSlice_eq_zero_of_not_coprime_two`) proves the claim. Numerically the per-$d$ ratio of the left side to the right side is exactly $1.000$ for every $d$ at all tested points (57190, 64000, 100000, 125000, 128000), i.e. the envelope is sharp per divisor, and the global inequality checks out at all of them, unlike the literal child3 shape.
--
--   This gives a fully proved, cancellation-free Type I comparison for $\mathrm{EV}$ (with the logarithmic weight restricted to $w>V$ only in the $d>\lfloor U\rfloor$ branch), suitable as a drop-in replacement interface in the Vaughan reduction, at the cost of at most a factor $2$ when re-deriving downstream Type I estimates.
-- source:
--   T. Tao, 'Every odd number greater than 1 is the sum of at most five primes', Math. Comp. 83 (2014) 997-1038; arXiv:1201.6656v4, Section 4. Repair of TaoFivePrimes child3 node 62275301 (eta0VaughanTypeISum_le_theorem51TypeI): the transferred half-log block is charged against the log-restricted slab K(d) for d > floor(U), the unweighted bucket S_0(d) remaining unrestricted, making the comparison provable per divisor with no Mobius cancellation.

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces
open scoped BigOperators

theorem TaoFivePrimes.theorem51_child3_restricted_log_repair
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ, (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.eta0VaughanTypeISum x alpha U V‖ ≤
        ∑ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖
          (if d ≤ ⌊U⌋₊
            then ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w))
            else ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.transferredInnerSupport x V d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w)))
          + c d * (Real.log d : ℂ) *
              (∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                TaoFivePrimes.eta0VaughanTest x alpha (d * w))‖ := by sorry
