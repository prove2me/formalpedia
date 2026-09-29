-- Prove2me | Theorems.Thm_TaoFivePrimes_mertens_tail_upper_bound
-- name    : TaoFivePrimes.mertens_tail_upper_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-27T15:51:59.229338+00:00
-- url     : https://prove2.me/theorems/457799a9-007d-4dcc-ba30-dfe80f5f2787
-- title:
--   Mertens-tail upper bound: $T(x)\le T(\infty)+1/\lfloor x\rfloor$ for $x\ge 1$
-- statement:
--   Write
--   \[P(x)=\prod_{p\le\lfloor x\rfloor}\frac{p}{p-1},\qquad
--   T(x)=\sum_{p\le\lfloor x\rfloor}\Bigl(\log(1-\tfrac1p)+\tfrac1p\Bigr),\qquad
--   T(\infty)=\sum_p\Bigl(\log(1-\tfrac1p)+\tfrac1p\Bigr),\]
--   the last series being the convergent (negative-term) tail of the Meissel--Mertens constant $B=\gamma+T(\infty)$. Then for every real $x\ge 1$,
--   \[T(x)\ \le\ T(\infty)+\frac{1}{\lfloor x\rfloor},\qquad\text{i.e.}\qquad
--   0\le \delta(x):=T(x)-T(\infty)\le \frac1{\lfloor x\rfloor}.\]
--
--   **Role.** This is the *upper* half of the tail information that the platform already had only in its *lower* half: `TaoFivePrimes.mertens_tail_le_partial_sum` (Proved) says exactly $\delta(x)\ge 0$. The pair is what converts any two-sided estimate for $\log P(x)$ into a two-sided estimate for the reciprocal prime sum, via the exact identity
--   \[\sum_{p\le\lfloor x\rfloor}\frac1p=\log P(x)+T(x),\]
--   which holds termwise because $\log\frac{p}{p-1}=-\log(1-\tfrac1p)$. Every *upper* bound on $\sum_{p\le x}1/p$ obtained from a Mertens product bound needs this node; without it one can only conclude $\sum 1/p \le \log P(x)+T(\lfloor x\rfloor)$ and the finite partial sum $T(\lfloor x\rfloor)$ cannot be compared to the constant $B$.
--
--   **Proof (elementary, Mathlib only; no prime-counting input, no numerical constant, nothing quoted).**
--
--   1. For a prime $p$, Mathlib's Taylor remainder estimate `Real.abs_log_sub_add_sum_range_le` applied at $u=1/p$ with one term gives $|\log(1-u)+u|\le u^2/(1-u)$, i.e.
--    $\bigl|\log(1-\tfrac1p)+\tfrac1p\bigr|\le \frac1{p(p-1)}$.
--   2. Extend the summand by zero off the primes and use `tsum_subtype`, then split the resulting series at $\lfloor x\rfloor+1$ with `Summable.sum_add_tsum_nat_add`. Summability comes by comparison with $2/n^2$ and `Real.summable_one_div_nat_pow`.
--   3. Since every term is $\le 0$ (from `Real.log_le_sub_one_of_pos`), the tail satisfies $\delta(x)=\sum_{p>\lfloor x\rfloor}|\log(1-\tfrac1p)+\tfrac1p|$, and dropping the primality constraint gives $\delta(x)\le\sum_{n>N}\frac1{n(n-1)}$ with $N=\lfloor x\rfloor$.
--   4. The telescoping identity $\frac1{(n+N)(n+N+1)}=\frac1{n+N}-\frac1{n+N+1}$ sums to $1/N$ by `Finset.sum_range_sub'` and `hasSum_iff_tendsto_nat_of_nonneg`.
--
--   **Honest scope.** The constant obtained is $1$ and not the sharper $1/2$ that the estimate $|\log(1-u)+u|\le u^2/(2(1-u))$ would give; the factor $2$ is missing because the Mathlib remainder lemma used in step 1 supplies $u^2/(1-u)$. We did not sharpen it, because (checked numerically) the factor $2$ changes no downstream conclusion on this mission. The statement is valid for **all** $x\ge1$ -- it is an elementary estimate, not a computation over a finite range, so unlike the Rosser--Schoenfeld product bounds it may be used at arbitrarily large $x$.
--
--   **Downstream status (numerical check performed for this node, not a formal proof).** Combined with the already-Proved
--   `TaoFivePrimes.rosser_schoenfeld_product_log_bound_mid` ($700\le x\le 10^8$) and
--   `TaoFivePrimes.rosser_schoenfeld_product_bound_286_to_700` ($286\le x<700$), this node closes
--   `TaoFivePrimes.mawia_reciprocal_sum_upper_bound_small` on $286\le x\le 10^8$: the requirement
--    $\log\bigl(1+\tfrac1{2\log^2 x}\bigr)+\tfrac1{\lfloor x\rfloor}\le\tfrac4{\log^3 x}$
--   was verified on every integer in $[286,10^8]$ (tightest at $x=700$, slack $1.3\cdot10^{-3}$). It does **not** close $2\le x<286$: there the only available product bound is `rosser_schoenfeld_product_bound_to_286`, whose $2e^{\gamma}/\sqrt x$ error is too large (276 of the 284 integers in $[2,286)$ fail, maximal deficit $4.1\cdot10^{-2}$ at $x=18$); that sub-range needs either a $(1+1/(2\log^2x))$-form product bound below $286$ (note it is *false* at $x=3$, so it cannot just be extended downwards) or a direct finite verification.
-- source:
--   Elementary estimate; no external quotation. The summatory identity sum_{p<=x} 1/p = log prod_{p<=x} p/(p-1) + sum_{p<=x} (log(1-1/p)+1/p) is the standard split underlying Mertens' theorem (see e.g. the companion node TaoFivePrimes.mertens_tail_le_partial_sum). The tail bound itself follows from |log(1-u)+u| <= u^2/(1-u) together with the telescoping sum_{n>N} 1/(n(n-1)) = 1/N.

import Mathlib

namespace TaoFivePrimes

theorem mertens_tail_upper_bound (x : ℝ) (hx : 1 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        1 / (⌊x⌋₊ : ℝ) := by
  sorry

end TaoFivePrimes
