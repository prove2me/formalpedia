-- Prove2me | Theorems.Thm_WangMinimaxRegret_Reformulation_eq_1
-- name    : WangMinimaxRegret.Reformulation.eq_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:20.108789+00:00
-- url     : https://prove2.me/theorems/c48f7420-0ad8-4679-911a-9ebb28383ef6
-- title:
--   Section 2, equation (1) — hypograph reformulation
-- statement:
--   Let the nonnegative valuation interval and finite moment information be consistent, and let $\mathcal F$ be the printed ambiguity class (including $F(a)=0$). Let $\mathcal M$ be the normalized Stieltjes payment class, with its cumulative allocation budget. For a payment $m\in\mathcal M$ and any real $r$, including negative $r$, the hypograph constraints satisfy
--   $$\bigl[\forall p\in I,\ rp\le\inf_{F\in\mathcal F,\ T_F(p)>0}R(m,F)/T_F(p)\bigr]\ \Longleftrightarrow\ r\le C(m).$$
--   Consequently the value of (1) equals the original robust-screening value $\sup_{m\in\mathcal M}C(m)$. Here $T_F(p)=F([p,\infty))$, $R(m,F)=\int m\,dF$, and $C(m)$ is the supremum of nonnegative rates that satisfy all original price-wise revenue inequalities. This is the hypograph reformulation of (P).
--
--   The statement also records the model agreement used by the page: if every $F\in\mathcal F$ has a finite strictly positive benchmark $B(F)=\sup_{p\in I}pT_F(p)$, then
--   $$C(m)=\inf_{F\in\mathcal F}R(m,F)/B(F).$$
--   For any finite upper bound $b$ and any $F\in\mathcal F$, the benchmark is attained by some price in $I$, as the displayed maximum requires. The finite-benchmark condition applies only to the quotient identification; it does not restrict the hypograph or value-equality clauses.
--
--   Differences from the source:
--   - encoding: real interval, payment functions, probability laws, and moment orders 1 through K → real-line Borel measures supported on the interval, Stieltjes functions extended by zero below a and constantly above finite b, and Fin K exponents i+1; reason: extensions only fix values outside the domain; all atoms and payment jumps are retained, including the payment atom at a>0
--   - encoding: the seller knows moments of an actual valuation distribution → Consistent d requires a nonempty printed ambiguity class, with finite specified moments; reason: makes the standing information-consistency assumption explicit; no interiority, positive variance, or density is assumed
--   - reading: the notation [a,b] also occurs with b=infinity later in the paper → b has type WithTop real; prices and valuations remain finite; hindsight revenue is a supremum, and the competitive ratio uses all price-wise revenue inequalities; reason: specifies the support-only unbounded cases where the printed ratio may be infinity/infinity; finite positive benchmarks retain the usual quotient
--   - encoding: nonnegative revenue integrals and optimization infima/suprema → nonnegative extended integrals and ENNReal/EReal extrema; zero-tail laws impose no fractional constraint; reason: avoids nonintegrable real integrals defaulting to zero and empty real extrema; empty infima are positive infinity
-- source:
--   Wang, Liu and Zhang (2024), Minimax Regret Robust Screening with Moment Information, https://doi.org/10.1287/msom.2023.0072, Section 2, p. 8, equation (1) and the immediately preceding ratio displays

import Definitions.Def_WangMinimaxRegret_Reformulation_Revenue

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

namespace WangMinimaxRegret.Reformulation

theorem eq_1 (d : Data) (hc : Consistent d) :
    (∀ (m : StieltjesFunction ℝ) (r : ℝ), IsPayment d m →
      (HypographFeasible d m r ↔ (r : EReal) ≤ (competitiveRatio d m : EReal))) ∧
    hypographValue d = originalValue d ∧
    (∀ m : StieltjesFunction ℝ, IsPayment d m →
      (∀ F : Measure ℝ, Ambiguous d F → 0 < benchmark d F ∧ benchmark d F < ⊤) →
      competitiveRatio d m = quotientRatio d m) ∧
    (∀ (b : ℝ) (F : Measure ℝ), d.b = (b : WithTop ℝ) → Ambiguous d F →
      ∃ p ∈ interval d, benchmark d F = priceRevenue F p) := by sorry

end WangMinimaxRegret.Reformulation
