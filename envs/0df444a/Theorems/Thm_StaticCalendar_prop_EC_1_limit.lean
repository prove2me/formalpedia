-- Prove2me | Theorems.Thm_StaticCalendar_prop_EC_1_limit
-- name    : StaticCalendar.prop_EC_1_limit
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:48.988149+00:00
-- url     : https://prove2.me/theorems/d744eafc-2868-49b3-86c2-977addffa3c4
-- title:
--   Proposition EC.1, limit clause (corrected: $\ge$ for non-integral $b$)
-- statement:
--   For real $b\ge1$ the limit $L=\lim_{T\to\infty}\Delta^{APX}(T,b)$ exists and
--
--   $$
--   L\ \ge\ 1-\frac{\lfloor b\rfloor^{\lfloor b\rfloor}}{\lfloor b\rfloor!}e^{-\lfloor b\rfloor}\qquad\text{and}\qquad L\ge1-\frac1e.
--   $$
--
--   When $b$ is a positive integer, $L=1-\frac{b^b}{b!}e^{-b}$. Together with the monotonicity in $T$, this gives (10).
--
--   Differences from the source:
--   - correction: $\lim_{T\to\infty}\Delta^{APX}=1-\lfloor b\rfloor^{\lfloor b\rfloor}e^{-\lfloor b\rfloor}/\lfloor b\rfloor!$ for every real $b$ → the limit exists, it is $\ge$ that value, with equality for integer $b$; reason: at $b=1.5$ the limit is $\mathbb E[\min\{\mathrm{Pois}(1.5),1.5\}]/1.5=0.66530$, not $1-1/e=0.63212$; the proof shows only $\ge$ for non-integral $b$
--   - encoding: $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$ → the explicit binomial sum `binomMinExp`; reason: the definition of the expectation of a function of a binomial variable; same value
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Proposition EC.1, p.ec14; proof, pp.ec14–ec15

import Mathlib
import Definitions.Def_StaticCalendar_deltaAPX

open MeasureTheory

namespace StaticCalendar

open Filter Topology in
/-- Proposition EC.1, limit clause, arXiv:1811.01077v5, pp.ec14–ec15, corrected: for real `b ≥ 1`
the limit `lim_{T→∞} Δ^{APX}` exists, it is at least `1 - ⌊b⌋^⌊b⌋ e^{-⌊b⌋}/⌊b⌋! ≥ 1 - 1/e`, and it
equals `1 - b^b e^{-b}/b!` when `b` is a positive integer.

**Formalization Note.** The printed equality at `⌊b⌋` is false for non-integral `b`: at `b = 1.5`
the limit is `E[min{Pois(1.5),1.5}]/1.5 = 0.66530`, not `1 - 1/e = 0.63212`. -/
theorem prop_EC_1_limit (b : ℝ) (hb : 1 ≤ b) :
    ∃ L : ℝ, Tendsto (fun T : ℕ => deltaAPX T b) atTop (𝓝 L) ∧
      1 - (⌊b⌋₊ : ℝ) ^ ⌊b⌋₊ * Real.exp (-(⌊b⌋₊ : ℝ)) / (⌊b⌋₊.factorial : ℝ) ≤ L ∧
      1 - Real.exp (-1) ≤ L ∧
      ∀ k : ℕ, b = k → L = 1 - (k : ℝ) ^ k * Real.exp (-(k : ℝ)) / (k.factorial : ℝ) := by sorry

end StaticCalendar
