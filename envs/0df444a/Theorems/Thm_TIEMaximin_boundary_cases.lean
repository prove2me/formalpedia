-- Prove2me | Theorems.Thm_TIEMaximin_boundary_cases
-- name    : TIEMaximin.boundary_cases
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:28.003499+00:00
-- url     : https://prove2.me/theorems/2365779e-9d60-41d5-9311-a23efaf92009
-- title:
--   §2 — boundary cases: uniform recipient for $m<n$ or $n=1$
-- statement:
--   Let $n\ge1$ and suppose $m<n$ or $n=1$. The mechanism that gives all goods to an agent chosen uniformly at random, independently of the reports, is truthful in expectation and ex-ante envy-free. At every nonnegative profile, every allocation $A$ in its support satisfies $v_i(A_i)\ge\mathrm{TPS}_i/6\ge\mathrm{MMS}_i/6$ for every agent $i$, and its support has at most $m(n-1)+1$ allocations. Moreover, if $m<n$ every TPS is zero.
--
--   These are the cases the paper sets aside before assuming $m\ge n\ge2$. The case without goods is $m=0<n$, whose only allocation is the empty one; for $n=1$ the sole agent receives all goods.
--
--   Differences from the source:
--   - reading: satisfies Theorem 1.1 → the existential and ex-post clauses of Theorem 1.1 and the support bound, for this mechanism; the polynomial-time computation of the lottery is carried by `theorem_1_1`; reason: the machine is uniform in n and m, so it cannot be stated per case
--   - encoding: n agents → `[NeZero n]`; reason: no allocation exists for n = 0 < m
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §2, p.8

import Mathlib
import Definitions.Def_TIEMaximin_Mechanism

namespace TIEMaximin

/-- **§2, the boundary cases** (p.8). If `m < n` or `n = 1`, giving all goods to an agent chosen
uniformly at random, independently of the reports, is truthful-in-expectation and ex-ante
envy-free and gives every agent at least `TPS_i/6 ≥ MMS_i/6` in every allocation of its support, with at most
`m(n − 1) + 1` allocations in the support; and if `m < n` every TPS is zero.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, §2, p.8: "If m < n, every TPS is zero,
... and giving all goods to an agent chosen uniformly at random, independently of the reports,
satisfies Theorem 1.1."

**Formalization Note.** For `n = 1` the mechanism gives the sole agent all goods, and `m = 0 < n`
is the case "without goods", whose only allocation is the empty one. The polynomial-time computation
of this lottery is carried by `theorem_1_1`. -/
theorem boundary_cases (n m : ℕ) [NeZero n] (h : m < n ∨ n = 1) :
    IsTIE (uniformRecipient n m) ∧ IsExAnteEF (uniformRecipient n m) ∧
    (∀ v : Fin n → Fin m → ℝ, Nonneg v → ∀ A ∈ (uniformRecipient n m v).support, ∀ i,
      tps n (v i) / 6 ≤ valOf (v i) i A ∧ mmsOf n (v i) / 6 ≤ tps n (v i) / 6) ∧
    (∀ v : Fin n → Fin m → ℝ, (uniformRecipient n m v).support.ncard ≤ m * (n - 1) + 1) ∧
    (m < n → ∀ u : Fin m → ℝ, (∀ g, 0 ≤ u g) → tps n u = 0) := by sorry

end TIEMaximin
