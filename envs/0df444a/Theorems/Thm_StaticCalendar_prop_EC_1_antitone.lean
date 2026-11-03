-- Prove2me | Theorems.Thm_StaticCalendar_prop_EC_1_antitone
-- name    : StaticCalendar.prop_EC_1_antitone
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:49.742965+00:00
-- url     : https://prove2.me/theorems/6aa7b37f-5dfe-4140-9255-f28a10719cae
-- title:
--   Proposition EC.1, first clause — $\Delta^{APX}$ is non-increasing in $T$
-- statement:
--   For real $b\ge1$, the sequence $T\mapsto\mathbb E[\min\{\mathrm{Bin}(T,b/T),b\}]/b$, for integers $T\ge b$, is non-increasing. The guarantee at a finite horizon is at least its limit as $T\to\infty$.
--
--   The paper asserts this without a proof.
--
--   Differences from the source:
--   - reading: "for all $b\le T$" → real $b\ge1$ and integers $T\ge b$; reason: $b\ge1$ is the standing normalization, stated on p.ec14
--   - encoding: $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$ → the explicit binomial sum `binomMinExp`; reason: the definition of the expectation of a function of a binomial variable; same value
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Proposition EC.1, p.ec14

import Mathlib
import Definitions.Def_StaticCalendar_deltaAPX

open MeasureTheory

namespace StaticCalendar

/-- Proposition EC.1, first clause, arXiv:1811.01077v5, p.ec14: for all `b ≤ T`,
`Δ^{APX} = E[min{Bin(T,b/T),b}]/b` is non-increasing in `T`.

**Formalization Note.** `1 ≤ b` is the paper's normalization ("we have normalized `b` such that
`b ≥ 1`", p.ec14). `b` is real. -/
theorem prop_EC_1_antitone (b : ℝ) (hb : 1 ≤ b) :
    AntitoneOn (fun T : ℕ => deltaAPX T b) {T : ℕ | b ≤ T} := by sorry

end StaticCalendar
