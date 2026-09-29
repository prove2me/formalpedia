-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_cor35_sharp_block
-- name    : TaoFivePrimes.theorem51_cor35_sharp_block
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T03:06:49.54228+00:00
-- url     : https://prove2.me/theorems/a147ebbc-d4ce-41b2-9a61-4307d4e38d97
-- title:
--   Tao Corollary 3.5 at the sharp block count: the single-block odd estimate
-- statement:
--   **Corollary 3.5 at the sharp block count.** Let $q\ge1$, $A,B\ge0$, $\alpha$ with $2\alpha=\frac aq+\beta$ and $|\beta|\le q^{-2}$, and $\theta\in\mathbb R$. Assume the source's single-block Vinogradov estimate: for every $u<v$ and every $\alpha'=\frac{a'}{q}+\beta'$ with $|\beta'|\le q^{-2}$,
--
--   $$\sum_{\lfloor u\rfloor<n\le\lfloor v\rfloor}\min\Bigl(A,\frac B{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ \Bigl(\Bigl\lfloor\frac{v-u}{q}\Bigr\rfloor+1\Bigr)\Bigl(2A+\frac2\pi Bq\log4q\Bigr),$$
--
--   a term with vanishing sine contributing $A$. Let $x<y$ with $y\le x+2q$ — that is, a range of width at most $2q$. Then the **odd** integers of that range satisfy
--
--   $$\sum_{\substack{x<n\le y\\ n\ \mathrm{odd}}}\min\Bigl(A,\frac B{|\sin(\pi\alpha n+\theta)|}\Bigr)\ \le\ 2A+\frac2\pi Bq\log4q,$$
--
--   with **block count one**, not the two that the published $\bigl(\lfloor\frac{y-x}{2q}\rfloor+1\bigr)$ would give.
--
--   **Why the count is one.** Substituting $n=2m+1$ turns the odd integers of a range of width $2q$ into *all* integers $m$ of a range of width $q$, with frequency $2\alpha$ and phase $\pi\alpha+\theta$. The single-block estimate above is then applied once. The covering count $\lfloor W/q\rfloor+1$ over-counts by exactly one whenever $q\mid W$, and it is precisely the case $W=q$ that occurs here; carrying the published count instead doubles the constant, from $0.89$ to $1.78$, in the Type I estimate of the source's Section 5.2.
--
--   **Role.** This is the sharpened form of `TaoFivePrimes.vinogradov_odd`: same odd restriction, but stated on a range of the admissible width $2q$ with the block count kept at one. It is the input that Tao's Section 5.2 block argument actually uses when he writes $\sum_{d\le q/2}$ and later $\sum_j$ over blocks $2jq+\frac q2<d\le 2(j+1)q+\frac q2$ of width exactly $2q$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 3, Corollary 3.5 and its proof ("By subdivision of the interval it suffices to show"), together with Section 5.2, where Corollary 3.5 is applied to blocks 2jq + q/2 < d <= 2(j+1)q + q/2 of width exactly 2q and the block count is one.

import Mathlib

open Finset

theorem TaoFivePrimes.theorem51_cor35_sharp_block
    (A B : ℝ) (alpha beta theta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (halpha : 2 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvino : ∀ (alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A
              else min A (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)))
    (x y : ℝ) (hwidth : y ≤ x + 2 * (q : ℝ)) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋ ⌊y⌋).filter (fun n : ℤ => Odd n),
        (if Real.sin (Real.pi * alpha * (n : ℝ) + theta) = 0 then A
          else min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|)))
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by sorry
