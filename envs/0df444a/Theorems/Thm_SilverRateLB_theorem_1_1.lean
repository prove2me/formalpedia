-- Prove2me | Theorems.Thm_SilverRateLB_theorem_1_1
-- name    : SilverRateLB.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:09.104795+00:00
-- url     : https://prove2.me/theorems/16780422-8f1b-424a-bf85-eb6b8b4243f6
-- title:
--   Theorem 1.1 — every nonnegative schedule has $\mathscr R_n(H)\ge n^{-(p_{\mathrm{sil}}+C\sqrt{\log\log n/\log n})}$
-- statement:
--   There is an absolute constant $C>0$ and a threshold $N$ such that for every $L>0$, every $n\ge N$ and every nonnegative stepsize schedule $H=(h_1,\dots,h_n)\in[0,\infty)^n$,
--   $$\mathscr R_n(H)\ \ge\ n^{-\left(p_{\mathrm{sil}}+C\sqrt{\log\log n/\log n}\right)},$$
--   where $\mathscr R_n(H)$ is the worst-case normalized function suboptimality (1) over convex $L$-smooth functions and $p_{\mathrm{sil}}=\log_2(1+\sqrt2)$.
--
--   Since the exponent tends to $p_{\mathrm{sil}}$, no predetermined nonnegative stepsize schedule achieves a rate $O(n^{-p})$ with $p>p_{\mathrm{sil}}$, so the silver rate $O(n^{-p_{\mathrm{sil}}})$ of Altschuler and Parrilo is optimal up to a subpolynomial factor.
--
--   Differences from the source:
--   - generalization: ℛ_n for one ambient smoothness constant L → ∀ L > 0, quantified after C and N; reason: one C and N for every L; specializes to any fixed L (footnote 6, p. 6, shows ℛ_n does not depend on L)
--   - reading: log (base not stated) → natural logarithm Real.log; reason: another base changes only C and N
--   - encoding: for every sufficiently large n → ∃ N, ∀ H with N ≤ H.length; reason: standard reading of “sufficiently large”
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n → H : List ℝ with nonnegative entries, n = H.length; reason: same schedules
--   - encoding: ℛ_n(H) a real supremum → worstCaseRate in ℝ≥0∞, bound written as ENNReal.ofReal; reason: the supremum is finite (proved in the verification file), so the comparison is the paper's
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Theorem 1.1, (2), p. 4

import Mathlib
import Definitions.Def_SilverRateLB_pSil
import Definitions.Def_SilverRateLB_worstCaseRate

open scoped ENNReal

namespace SilverRateLB

/-- **Theorem 1.1 (finite-horizon error lower bound).** There is an absolute constant `C > 0`
such that for every sufficiently large `n` and every schedule `H ∈ [0,∞)^n`,
`ℛ_n(H) ≥ n^{−(p_sil + C√(log log n / log n))}`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Theorem 1.1, (2), p. 4.

**Formalization Note** `C` and the threshold `N` are chosen before `L` and `H`, so they are
uniform over all schedules. `L > 0` is universal (the paper's `ℛ_n` has an ambient `L`;
footnote 6, p. 6, reduces every `L` to `L = 1`). `log` is the natural logarithm. A schedule is a
`List ℝ` with nonnegative entries and `n` is its length. `worstCaseRate` is valued in `ℝ≥0∞`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ L : ℝ, 0 < L → ∀ H : List ℝ, (∀ h ∈ H, 0 ≤ h) →
      N ≤ H.length →
      ENNReal.ofReal ((H.length : ℝ) ^ (-(pSil + C * Real.sqrt
          (Real.log (Real.log H.length) / Real.log H.length)))) ≤ worstCaseRate L H := by sorry

end SilverRateLB
