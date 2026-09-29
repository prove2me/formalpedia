-- Prove2me | Theorems.Thm_TateCurve_tsum_succ_prod_eq_tsum_divisors
-- name    : TateCurve.tsum_succ_prod_eq_tsum_divisors
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ebc068ac-c5b3-508a-897d-38dbe836b001
-- title:
--   Regrouping a double series into divisor sums
-- statement:
--   Let $K$ be a nontrivially normed field which is complete, let $h : \mathbb{N} \to K$ be a sequence, let $C$ be a real number and $r \in K$. Assume $1 \le C$, that $\|h(m)\| \le C^{m}$ for every natural number $m > 0$ (no condition is imposed on $h(0)$), and that $\|r\| \cdot C < 1$. Then the unordered sum over all pairs $p = (p_1, p_2)$ of natural numbers of $h(p_2+1)\, r^{(p_1+1)(p_2+1)}$ equals the unordered sum over all natural numbers $N$ of $\bigl(\sum_{d \mid N+1} h(d)\bigr) r^{N+1}$, the inner sum being over the divisor finset `Nat.divisors` of $N+1$, i.e. over the positive divisors of $N+1$. Both sides are Mathlib `tsum`s, so the assertion is an equality of the two sums in the sense of unconditional convergence in $K$ (with the convention that a non-summable family has sum $0$); under the stated hypotheses the left-hand family is in fact summable. No ultrametric assumption on the norm is made.
--
--   This is the combinatorial regrouping that turns a double product series $\sum_{n,m \ge 1} h(m) r^{nm}$ into a $q$-expansion whose $N$-th coefficient is the divisor sum $\sum_{d \mid N} h(d)$. It is used in the construction of the Tate curve, supplying the $q$-expansions of the coordinate functions [`TateCurve.pointX_qExpansion`](thm.html#TateCurve.pointX_qExpansion) and [`TateCurve.pointY_qExpansion`](thm.html#TateCurve.pointY_qExpansion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_tsum_succ_prod_eq_tsum_divisors.lean

import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.SpecificLimits.Normed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem TateCurve.tsum_succ_prod_eq_tsum_divisors {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) : ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) := by sorry
