-- Prove2me | Theorems.Thm_StaticCalendar_virtRev_eq
-- name    : StaticCalendar.virtRev_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:41.628696+00:00
-- url     : https://prove2.me/theorems/ea6fe25c-99ae-48ac-bb4c-88aee7829399
-- title:
--   Step 2 — the virtual calendar sells a truncated sum
-- statement:
--   Let $x$ be feasible for CDLP-S and $c\ge0$. With $k$ periods, the virtual calendar earns
--
--   $$
--   J_{\mathsf C}=\sum_{i=1}^n p_{\mathsf C,i}\ \mathbb E\Big[\min\Big\{\sum_{t=1}^{k}Q_i(\xi_t),\,c_i\Big\}\Big],
--   $$
--
--   where the $Q_i(\xi_t)$ are independent copies of the item demand (EC.7). Each item's sales are the sum of its $k$ demands, truncated once by the starting inventory.
--
--   Differences from the source:
--   - generalization: $x^*$ an optimal solution of CDLP-S → any feasible $x$; reason: feasibility, constraints (6)–(8), is all the argument uses; an optimal solution is feasible
--   - generalization: starting inventory $b$ and $T$ periods → any $c\ge0$ and any $k$; reason: the identity needs nothing about $b$ or $T$, and $c=b$, $k=T$ is the source
--   - reading: the virtual demand CDF $\sum_S x(S)\sum_j F_{(i,j,S)}$, p.ec10, and the variable $Q_i$ of (EC.7) → the law of $Q_i$, `nuItem`; reason: the printed CDF omits the atom at $0$ from assortments without $i$; (EC.7) fixes the intended law
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Step 2, p.ec13

import Mathlib
import Definitions.Def_StaticCalendar_IsLPFeasible
import Definitions.Def_StaticCalendar_virtRev

open MeasureTheory

namespace StaticCalendar

/-- Step 2, arXiv:1811.01077v5, p.ec13: under the virtual calendar "the total sales of inventory `i`
is a sum of `T` trials of independent random variables `Qᵢ`, truncated by the starting inventory
`bᵢ`", so its revenue is `Σᵢ p_{C,i} E[min{Σₜ Qᵢ(ξₜ), bᵢ}]`, with `Qᵢ` as in (EC.7). -/
theorem virtRev_eq {n m T : ℕ} (I : DemandModel n m) (b : Fin n → ℝ) (x : Assortment n m → ℝ)
    (hx : IsLPFeasible I T b x) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (k : ℕ) :
    virtRev I x c k =
      ∑ i, pC I x i * ∫ ω, min (∑ t, ω t) (c i) ∂(Measure.pi fun _ : Fin k => nuItem I x i) := by sorry

end StaticCalendar
