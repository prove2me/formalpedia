-- Prove2me | Theorems.Thm_SubspaceConv_eq_24_25
-- name    : SubspaceConv.eq_24_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:34.333203+00:00
-- url     : https://prove2.me/theorems/78b9e389-7839-4b24-bea9-b0d2712c2f49
-- title:
--   Eqs. (24)–(25) — $|\mathrm{Gr}_q(n,r)|$: product formula, $\Theta_q(q^{r(n-r)})$, symmetry and recurrence
-- statement:
--   Let $q=|\mathbb F_q|$ and $0\le r\le n$. Counting ordered bases gives
--   $$|\mathrm{Gr}_q(n,r)|=\prod_{i=0}^{r-1}\frac{q^n-q^i}{q^r-q^i}=q^{r(n-r)}\prod_{i=0}^{r-1}\frac{1-q^{i-n}}{1-q^{i-r}}=\Theta_q\big(q^{r(n-r)}\big),\tag{24}$$
--   uniformly in $n,r$: the last product is between $1$ and $\prod_{i\ge1}(1-q^{-i})^{-1}<\infty$. Precisely:
--
--   1. $|\mathrm{Gr}_q(n,r)|\cdot\prod_{i=0}^{r-1}(q^r-q^i)=\prod_{i=0}^{r-1}(q^n-q^i)$;
--   2. $q^{r(n-r)}\le|\mathrm{Gr}_q(n,r)|$;
--   3. $|\mathrm{Gr}_q(n,r)|\cdot\prod_{j=1}^{r}(1-q^{-j})\le q^{r(n-r)}$;
--   4. $|\mathrm{Gr}_q(n,r)|=|\mathrm{Gr}_q(n,n-r)|$ (annihilators);
--   5. $|\mathrm{Gr}_q(0,0)|=1$ and, for $1\le r\le n$,
--   $$|\mathrm{Gr}_q(n,r)|=|\mathrm{Gr}_q(n-1,r)|+q^{n-r}|\mathrm{Gr}_q(n-1,r-1)|;\tag{25}$$
--   at $r=0$, where $|\mathrm{Gr}_q(n-1,-1)|=0$ by the convention of §2, (25) reads $|\mathrm{Gr}_q(n,0)|=|\mathrm{Gr}_q(n-1,0)|$ for $n\ge1$.
--
--   These counts drive the logarithmic bound $\log_qM_q(n,k)=\Omega(nk)$ used to convert $O_q(nkM_q(n,k))$ into $O_q(M_q(n,k)\log M_q(n,k))$.
--
--   **Formalization Note** Item 3 implies the printed upper bound, since $\prod_{j=1}^r(1-q^{-j})\ge\prod_{j\ge1}(1-q^{-j})>0$. The second form of (24) and the formula $[r]_q=|\mathrm{Gr}_q(r,1)|=(q^r-1)/(q-1)$ follow from item 1.
--
--   Differences from the source:
--   - encoding: the product formula with division → the product formula multiplied out over ℕ; reason: q^r − q^i > 0 for i < r
--   - encoding: = Θ_q(q^{r(n−r)}), uniformly in n, r → the explicit bounds q^{r(n−r)} ≤ |Gr_q(n, r)| and |Gr_q(n, r)|·∏_{j=1}^{r}(1 − q^{−j}) ≤ q^{r(n−r)}; reason: these are the two sides of the uniform estimate
--   - generalization: "the last product is between 1 and ∏_{i≥1}(1 − q^{−i})^{−1}" → upper bound with the finite product ∏_{j=1}^{r}(1 − q^{−j})^{−1}; reason: the finite product is at least the infinite one, so the Lean bound implies the printed one
--   - encoding: (25) for 0 ≤ r ≤ n, with |Gr_q(n − 1, −1)| = 0 (§2, p.10) → (25) for 1 ≤ r ≤ n, plus |Gr_q(n + 1, 0)| = |Gr_q(n, 0)|; reason: natural-number arithmetic (r − 1 at r = 0); every instance of the printed identity is covered
--   - encoding: the second form q^{r(n−r)}∏(1 − q^{i−n})/(1 − q^{i−r}) and [r]_q = |Gr_q(r, 1)| = (q^r − 1)/(q − 1) → not separate clauses; reason: both are algebraic consequences of clause 1 (the latter at n = r, r = 1)
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), Appendix A, eqs. (24)–(25), p.21 (PDF p.22)

import Mathlib
import Definitions.Def_MinrankTW_gaussCount

namespace SubspaceConv

/-- **Eqs. (24)–(25)** (Counting subspaces), Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), Appendix A, p.21 (PDF p.22). For
`0 ≤ r ≤ n`: `|Gr_q(n, r)| = ∏_{i=0}^{r−1} (q^n − q^i)/(q^r − q^i)
= q^{r(n−r)} ∏_{i=0}^{r−1} (1 − q^{i−n})/(1 − q^{i−r}) = Θ_q(q^{r(n−r)})`, uniformly (the last
product is between `1` and `∏_{i≥1}(1 − q^{−i})^{−1}`); `|Gr_q(n, r)| = |Gr_q(n, n − r)|`; and,
from `|Gr_q(0, 0)| = 1`, `|Gr_q(n, r)| = |Gr_q(n − 1, r)| + q^{n−r}|Gr_q(n − 1, r − 1)|`.

**Formalization Note** `q = |F|`. `|Gr_q(n, j)|` is the published definition `MinrankTW.gaussCount F n j` (the number of
`j`-dimensional subspaces of `Fin n → F`, reused from the companion mission). The product formula is multiplied out (no division). The
`Θ_q` estimate is the two bounds `q^{r(n−r)} ≤ |Gr_q(n, r)|` and
`|Gr_q(n, r)| ∏_{j=1}^{r}(1 − q^{−j}) ≤ q^{r(n−r)}` (in `ℝ`); the second implies the printed upper
bound by the infinite product, since `∏_{j=1}^{r}(1 − q^{−j}) ≥ ∏_{j≥1}(1 − q^{−j}) > 0`.
(25) is stated for `1 ≤ r ≤ n`, and its `r = 0` instance, where `|Gr_q(n − 1, −1)| = 0` by the
convention of §2 (p.10), is the separate clause `|Gr_q(n + 1, 0)| = |Gr_q(n, 0)|`. -/
theorem eq_24_25 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (∀ n r : ℕ, r ≤ n →
      MinrankTW.gaussCount F n r *
          ∏ i ∈ Finset.range r, (Fintype.card F ^ r - Fintype.card F ^ i) =
        ∏ i ∈ Finset.range r, (Fintype.card F ^ n - Fintype.card F ^ i)) ∧
    (∀ n r : ℕ, r ≤ n → Fintype.card F ^ (r * (n - r)) ≤ MinrankTW.gaussCount F n r) ∧
    (∀ n r : ℕ, r ≤ n →
      (MinrankTW.gaussCount F n r : ℝ) *
          ∏ j ∈ Finset.Icc 1 r, (1 - (Fintype.card F : ℝ) ^ (-(j : ℤ))) ≤
        (Fintype.card F : ℝ) ^ (r * (n - r))) ∧
    (∀ n r : ℕ, r ≤ n → MinrankTW.gaussCount F n r = MinrankTW.gaussCount F n (n - r)) ∧
    MinrankTW.gaussCount F 0 0 = 1 ∧
    (∀ n : ℕ, MinrankTW.gaussCount F (n + 1) 0 = MinrankTW.gaussCount F n 0) ∧
    (∀ n r : ℕ, 1 ≤ r → r ≤ n →
      MinrankTW.gaussCount F n r =
        MinrankTW.gaussCount F (n - 1) r +
          Fintype.card F ^ (n - r) * MinrankTW.gaussCount F (n - 1) (r - 1)) := by sorry

end SubspaceConv
