-- Prove2me | Theorems.Thm_StaticCalendar_rev_ge_virtRev
-- name    : StaticCalendar.rev_ge_virtRev
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:41.819795+00:00
-- url     : https://prove2.me/theorems/6c4b1757-210d-4283-936f-51462a69da36
-- title:
--   Step 1, Case 1 — Algorithm 1 earns at least the virtual calendar
-- statement:
--   Assume Assumption 2 and let $x$ be feasible for CDLP-S. For all inventories $c\ge0$ and all $t$,
--
--   $$
--   \mathsf{Rev}(c,t)\ \ge\ J_{\mathsf C}(c,t),
--   $$
--
--   where $\mathsf{Rev}(c,t)$ is the expected revenue of Algorithm 1 with inventories $c$ at the start of period $t$, and $J_{\mathsf C}(c,t)$ is that of the virtual calendar.
--
--   This reduces Theorem 1 from a coupled multi-item system with correlated demand to a sum of independent one-item problems.
--
--   Differences from the source:
--   - generalization: $x^*$ an optimal solution of CDLP-S → any feasible $x$; reason: feasibility, constraints (6)–(8), is all the argument uses; an optimal solution is feasible
--   - generalization: periods $t\in[T]$, that is, at most $T$ remaining periods → every number $k$ of remaining periods; reason: stationarity makes $\mathsf{Rev}$ and $J_{\mathsf C}$ depend on $t$ through $k=T-t+1$ only, and $k\le T$ is a special case
--   - reading: the virtual demand CDF $\sum_S x(S)\sum_j F_{(i,j,S)}$, p.ec10, and the variable $Q_i$ of (EC.7) → the law of $Q_i$, `nuItem`; reason: the printed CDF omits the atom at $0$ from assortments without $i$; (EC.7) and $\rho_i$ fix the intended law
--   - encoding: the virtual calendar is specified item by item → demands independent across items; reason: the revenue is a sum of one-item revenues, so any coupling gives the same value
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Step 1, Case 1, pp.ec11–ec12; J_C and Rev, pp.ec10–ec11

import Mathlib
import Definitions.Def_StaticCalendar_Assumption2
import Definitions.Def_StaticCalendar_IsLPFeasible
import Definitions.Def_StaticCalendar_algRev
import Definitions.Def_StaticCalendar_virtRev

open MeasureTheory

namespace StaticCalendar

/-- Step 1, Case 1, arXiv:1811.01077v5, pp.ec11–ec12: `Rev(c,t) ≥ J_C(c,t)` for all `c ≥ 0`, "the
expected revenue earned from deterministic assortment `S_C` is a lower bound to the probabilistic
offering of assortments from Algorithm 1".

**Formalization Note.** `k = T - t + 1` is the number of remaining periods. Stationarity makes
`Rev` and `J_C` depend on `t` through `k` only. The statement holds for every `k`. -/
theorem rev_ge_virtRev {n m T : ℕ} (I : DemandModel n m) (b : Fin n → ℝ)
    (x : Assortment n m → ℝ) (h2 : Assumption2 I) (hx : IsLPFeasible I T b x)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (k : ℕ) :
    virtRev I x c k ≤ algRev I x c k := by sorry

end StaticCalendar
