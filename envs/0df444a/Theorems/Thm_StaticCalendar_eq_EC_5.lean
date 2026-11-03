-- Prove2me | Theorems.Thm_StaticCalendar_eq_EC_5
-- name    : StaticCalendar.eq_EC_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:29.777305+00:00
-- url     : https://prove2.me/theorems/138f99ca-4a9b-48ea-ade4-77acf776da86
-- title:
--   (EC.5) — truncation favors the virtual price
-- statement:
--   Assume Assumption 2, let $x$ be feasible for CDLP-S, and let $i$ be an item and $c\in[0,1]$. Then
--
--   $$
--   \frac{\sum_{S\in\mathcal S}x(S)\sum_{j:(i,j)\in S}p_j\,\mathbb E_{Q\sim F_{(i,j,S)}}[\min\{c,Q\}]}{\sum_{S\in\mathcal S}x(S)\sum_{j:(i,j)\in S}\mathbb E_{Q\sim F_{(i,j,S)}}[\min\{c,Q\}]}\ \ge\ p_{\mathsf C,i}.
--   $$
--
--   When $c$ units of item $i$ remain, the revenue per unit sold under Algorithm 1 is at least the virtual price. The inequality is what allows the backward induction of Step 1 to replace Algorithm 1 by the virtual calendar.
--
--   Differences from the source:
--   - encoding: (EC.5) as a ratio → cross-multiplied; reason: the denominator can vanish, and then both sides of the product form are $0$
--   - generalization: $x^*$ an optimal solution of CDLP-S → any feasible $x$; reason: feasibility, constraints (6)–(8), is all the argument uses; an optimal solution is feasible
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, (EC.5), p.ec11

import Mathlib
import Definitions.Def_StaticCalendar_Assumption2
import Definitions.Def_StaticCalendar_IsLPFeasible
import Definitions.Def_StaticCalendar_pC

open MeasureTheory

namespace StaticCalendar

/-- (EC.5), arXiv:1811.01077v5, p.ec11: under Assumption 2, for every item `i` and `c ∈ [0,1]`,
`Σ_S x(S) Σ_j p_j E[min{c,Q}] / Σ_S x(S) Σ_j E[min{c,Q}] ≥ p_{C,i}`.

**Formalization Note.** Cross-multiplied, as the printed denominator can vanish. -/
theorem eq_EC_5 {n m T : ℕ} (I : DemandModel n m) (b : Fin n → ℝ) (x : Assortment n m → ℝ)
    (h2 : Assumption2 I) (hx : IsLPFeasible I T b x) (i : Fin n) (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    pC I x i * ∑ S ∈ I.family, x S * ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ S),
        ∫ Q, min c (Q (i, j)) ∂I.D S ≤
      ∑ S ∈ I.family, x S * ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ S),
        I.p j * ∫ Q, min c (Q (i, j)) ∂I.D S := by sorry

end StaticCalendar
