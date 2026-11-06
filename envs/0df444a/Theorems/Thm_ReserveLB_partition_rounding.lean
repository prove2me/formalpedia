-- Prove2me | Theorems.Thm_ReserveLB_partition_rounding
-- name    : ReserveLB.partition_rounding
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:22.654211+00:00
-- url     : https://prove2.me/theorems/529f8157-caa1-4be7-a5bf-974501d73f95
-- title:
--   Section 4.1 — partition rounding adding at most $2\nu$ per packing row
-- statement:
--   Let the variables $v$ be partitioned into groups, let $x \ge 0$ have mass $\sum_{v \in g} x_v = 1$ in every group $g$, let $A \ge 0$ be a matrix of packing rows whose columns all have sum at most $\nu$, and let $c$ be an objective. Then there is a selection of one variable $\mathrm{sel}(g)$ in every group, with $x_{\mathrm{sel}(g)} > 0$, such that
--   $$
--   \sum_g A_{r,\mathrm{sel}(g)} \le \sum_v A_{rv}x_v + 2\nu\quad\text{for every row } r,\qquad \sum_g c_{\mathrm{sel}(g)} \le \sum_v c_v x_v .
--   $$
--
--   This is the rounding step of Lemma 4.1: one complete pattern per original, with every weighted row exceeded by at most $2\nu$ and the exceptional objective not increased.
--
--   Differences from the source:
--   - generalization: nonnegative rational columns, rational objective → real data; reason: the iterative-refinement argument works over the reals; rational data is a special case
--   - encoding: columns of sum at most ν → Σ_r A r v ≤ ν for every v, and 0 ≤ ν stated; reason: 0 ≤ ν follows from the column sums when there is a variable; it excludes only the empty case, where the claim would read 0 ≤ 2ν
--   - encoding: unit-mass groups, packing rows → a group map grp : V → G with Σ_{grp v = g} x v = 1; rows indexed by a finite type; reason: Lean convention; same instances
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 4.1, p.6

import Mathlib

namespace ReserveLB

/-- **Section 4.1 — partition rounding.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 4.1, p.6: "For nonnegative rational columns of sum at most ν, select one supported
variable per unit-mass group, adding at most 2ν to each packing row without increasing a rational
objective."

Let the variables `v` be partitioned into groups, let `x ≥ 0` have mass one in every group, let
`A ≥ 0` be a matrix of packing rows whose every column sums to at most `ν`, and let `c` be an
objective. Then one can select one variable `sel(g)` with `x_(sel(g)) > 0` in every group `g` so
that every row `r` satisfies `Σ_g A_(r, sel(g)) ≤ Σ_v A_rv x_v + 2ν` and
`Σ_g c_(sel(g)) ≤ Σ_v c_v x_v`.

**Formalization Note.** Real data (the paper's are rational); `ν ≥ 0` is stated, which follows
from the column sums whenever there is a variable. -/
theorem partition_rounding {V G Rw : Type*} [Fintype V] [Fintype G] [Fintype Rw] [DecidableEq G]
    (grp : V → G) (x : V → ℝ) (hx0 : ∀ v, 0 ≤ x v)
    (hx1 : ∀ g, ∑ v ∈ Finset.univ.filter (fun v => grp v = g), x v = 1)
    (A : Rw → V → ℝ) (hA : ∀ r v, 0 ≤ A r v) (ν : ℝ) (hν0 : 0 ≤ ν)
    (hν : ∀ v, ∑ r, A r v ≤ ν) (c : V → ℝ) :
    ∃ sel : G → V, (∀ g, grp (sel g) = g ∧ 0 < x (sel g)) ∧
      (∀ r, ∑ g, A r (sel g) ≤ ∑ v, A r v * x v + 2 * ν) ∧
      ∑ g, c (sel g) ≤ ∑ v, c v * x v := by sorry

end ReserveLB
