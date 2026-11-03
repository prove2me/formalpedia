-- Prove2me | Theorems.Thm_StaticCalendar_telescoping_bound
-- name    : StaticCalendar.telescoping_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:44.72914+00:00
-- url     : https://prove2.me/theorems/b802439e-40d1-4f47-a985-a639559de2d5
-- title:
--   Proof of Proposition EC.1 — the telescoping bound (corrected: last line only)
-- statement:
--   Let $1\le b\le T$ be integers and $a=b/T$. Then
--
--   $$
--   \frac{\mathbb E[\min\{\mathrm{Bin}(T,a),b\}]}{b}\ \ge\ 1+a^T-\binom Tb a^b(1-a)^{T-b}.
--   $$
--
--   This finite-horizon lower bound gives the limit of $\Delta^{APX}$ for integer $b$.
--
--   Differences from the source:
--   - correction: the chain $b\Delta^{APX}\ge b(1+a^T-C^b_{T-1}a^b(1-a)^{T-b-1})=b(1+a^T-C^b_Ta^b(1-a)^{T-b})$ → only the last expression; reason: the middle expression is false at $T=b$: then $a=1$, $\Delta^{APX}=1$, and the printed middle value is $2$ under $0^0=1$; the two expressions agree for $b<T$
--   - encoding: $b\Delta^{APX}\ge b(\cdots)$ → divided by $b>0$; reason: same inequality
--   - encoding: $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$ → the explicit binomial sum `binomMinExp`; reason: the definition of the expectation of a function of a binomial variable; same value
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Proof of Proposition EC.1, p.ec14

import Mathlib
import Definitions.Def_StaticCalendar_deltaAPX

open MeasureTheory

namespace StaticCalendar

/-- The telescoping bound in the proof of Proposition EC.1, arXiv:1811.01077v5, p.ec14: for a
positive integer `b ≤ T` and `a = b/T`, `bΔ^{APX} ≥ b(1 + a^T - C_T^b a^b (1-a)^{T-b})`.

**Formalization Note.** This is the last line of the display. The line before it,
`b(1 + a^T - C_{T-1}^b a^b (1-a)^{T-b-1})`, agrees with it for `b < T` and is false at `b = T`. -/
theorem telescoping_bound (T b : ℕ) (hb : 1 ≤ b) (hbT : b ≤ T) :
    1 + ((b : ℝ) / T) ^ T - (T.choose b : ℝ) * ((b : ℝ) / T) ^ b * (1 - (b : ℝ) / T) ^ (T - b) ≤
      deltaAPX T b := by sorry

end StaticCalendar
