-- Prove2me | Theorems.Thm_SilverRateLB_Supplement_theorem_1_2
-- name    : SilverRateLB.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:47:31.319205+00:00
-- url     : https://prove2.me/theorems/d76e04b5-4dd8-4b7f-a2c5-760348329cf2
-- title:
--   Theorem 1.2 — anytime error lower bound at exponent $p_{\mathrm{any}}$
-- statement:
--   Let
--   $$
--   p_{\mathrm{any}}:=\frac{2p_{\mathrm{sil}}}{1+p_{\mathrm{sil}}},
--   $$
--   and let $H=(h_t)_{t\ge1}$ be one infinite sequence of nonnegative stepsizes, fixed across all horizons, with $H_n=(h_1,\ldots,h_n)$. There is an absolute constant $C>0$, independent of $H$, such that for every ambient smoothness constant $L>0$,
--   $$
--   \mathscr R_n(H_n)\ge n^{-\left(p_{\mathrm{any}}+C\sqrt{\log\log n/\log n}\right)}
--   $$
--   for infinitely many $n$.
--
--   Thus no single nonnegative stepsize schedule can have worst-case error asymptotically better than the anytime silver exponent at every stopping time.
--
--   **Formalization Note** `H t` represents $h_{t+1}$, `schedulePrefix H n` is $H_n$, and the infinite set of horizons is stated with `Set.Infinite`. The worst-case rate is the published $[0,\infty]$-valued definition.
--
--   Differences from the source:
--   - generalization: $\mathscr R_n$ for one ambient smoothness constant $L$ → $\forall L>0$, quantified after $C$ and $H$; reason: the same absolute $C$ works for every $L$, and this specializes to any fixed $L$ by the paper's rescaling convention
--   - reading: $\log$ (base not stated) → natural logarithm `Real.log`; reason: another fixed base changes only the absolute constant
--   - encoding: $H=(h_t)_{t\ge1}$ and $H_n=(h_1,\ldots,h_n)$ → `H : ℕ → ℝ` with `H t = h_{t+1}` and `schedulePrefix H n`; reason: the same infinite schedules and prefixes, with a zero-based index
--   - encoding: for infinitely many $n$ → `Set.Infinite` of the horizons satisfying the bound; reason: literal Lean expression of the paper's quantifier
--   - encoding: $\mathscr R_n(H_n)$ a real supremum → `worstCaseRate` in $ℝ_{≥0}^{\infty}$ and the lower bound embedded by `ENNReal.ofReal`; reason: the published rate uses the extended codomain to avoid a junk real supremum, and is finite on these schedules
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Theorem 1.2, (3), p. 5; proof §C.2, pp. 32–33

import Mathlib
import Definitions.Def_SilverRateLB_Supplement_pAny
import Definitions.Def_SilverRateLB_worstCaseRate

open scoped ENNReal

namespace SilverRateLB.Supplement

/-- **Theorem 1.2 (anytime error lower bound).** There is an absolute constant `C > 0` such
that every infinite nonnegative schedule `H = (h_t)_{t≥1}` satisfies
`ℛ_n(H_n) ≥ n^{−(p_any + C√(log log n / log n))}` for infinitely many `n`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152,
Theorem 1.2, (3), p. 5.

**Formalization Note** `C` is chosen before `H` and `L`, hence is uniform over all schedules
and ambient smoothness constants. `H t` is the 1-based paper entry `h_{t+1}`, and
`schedulePrefix H n` is the single schedule's prefix `H_n`. "Infinitely many" is expressed
literally by `Set.Infinite`. `log` is the natural logarithm, and `worstCaseRate` is valued in
`ℝ≥0∞`. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ → ℝ, (∀ t, 0 ≤ H t) → ∀ L : ℝ, 0 < L →
      Set.Infinite {n : ℕ |
        ENNReal.ofReal ((n : ℝ) ^ (-(pAny + C * Real.sqrt
          (Real.log (Real.log n) / Real.log n)))) ≤
            SilverRateLB.worstCaseRate L (schedulePrefix H n)} := by sorry

end SilverRateLB.Supplement
