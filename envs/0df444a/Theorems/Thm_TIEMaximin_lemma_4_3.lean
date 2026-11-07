-- Prove2me | Theorems.Thm_TIEMaximin_lemma_4_3
-- name    : TIEMaximin.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:44.366006+00:00
-- url     : https://prove2.me/theorems/02589772-5183-4206-98ca-738c2ec7280a
-- title:
--   Lemma 4.3 — rounding a fractional suballocation on reciprocal grids
-- statement:
--   Let $v$ be a nonnegative profile and $b$ a fractional suballocation, viewed as a matrix with $n$ rows. Suppose that, for every agent $i$, every coordinate of row $i$ strictly between zero and one is a multiple of $1/k_i$ for a positive integer $k_i$. Then there is a finite lottery over integral suballocations that implements $b$, preserves all coordinates equal to one, and in which every supported suballocation $A$ satisfies
--
--   $$|v_i(A_i)-v_i(b_i)|\le\Bigl(1-\frac1{k_i}\Bigr)\max_{g\in M:\,0<b_{ig}<1}v_i(g)\quad\text{for every agent }i,$$
--
--   where an empty maximum is zero.
--
--   This is the third step of the mechanism, and the source of the loss term in the ex-post bound.
--
--   Differences from the source:
--   - encoding: finite lottery → `PMF` on a finite type, expectations as finite sums; reason: a distribution on a finite type is finite; same instances
--   - encoding: fractional suballocation; multiple of 1/k_i → entries in [0,1], column sums at most 1; b_ig = c/k_i with c a natural number; reason: §2's definition; the entries are positive
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 4.3, eq. (15), p.21

import Mathlib
import Definitions.Def_TIEMaximin_Rounding

namespace TIEMaximin

/-- **Lemma 4.3** (p.21). Let `b` be a fractional suballocation such that, for every agent `i`, every
coordinate of row `i` strictly between zero and one is a multiple of `1/k_i` for a positive
integer `k_i`. Then there is a finite lottery over integral suballocations that implements `b`,
preserves all coordinates equal to one, and in which every supported suballocation satisfies (15).

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 4.3, eq. (15), p.21.

**Formalization Note.** The lottery depends on `v` (the proof uses each agent's value order), so
`v` is quantified before `μ`. The three properties are `IsRounding`. `b` being a fractional
suballocation means entries in `[0, 1]` and column sums at most one (§2, p.6). -/
theorem lemma_4_3 {n m : ℕ} (v b : Fin n → Fin m → ℝ) (hv : Nonneg v)
    (hb : ∀ i g, 0 ≤ b i g ∧ b i g ≤ 1) (hcol : ∀ g, ∑ i, b i g ≤ 1)
    (k : Fin n → ℕ) (hk : ∀ i, 0 < k i)
    (hgrid : ∀ i g, 0 < b i g → b i g < 1 → ∃ c : ℕ, b i g = (c : ℝ) / (k i : ℝ)) :
    ∃ μ : PMF (SubAlloc n m), IsRounding v b k μ := by sorry

end TIEMaximin
