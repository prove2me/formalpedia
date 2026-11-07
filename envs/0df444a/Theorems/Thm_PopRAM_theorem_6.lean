-- Prove2me | Theorems.Thm_PopRAM_theorem_6
-- name    : PopRAM.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:25:52.129764+00:00
-- url     : https://prove2.me/theorems/fb139ff8-2f8c-46f0-84fe-051bd635e9ed
-- title:
--   Theorem 6 — the phase clock: each of the first $n^a$ rounds lasts $\le D\log n$ time and contains a common-round interval of $c\log n$ time, whp
-- statement:
--   For all constants $a,c,\eta>0$ there are a number of phases $m\ge1$ and a constant $D>0$, depending only on $a,c,\eta$, and $n_0$, such that for all $n\ge n_0$ the following holds. Start the clock with $m$ phases from the standard initialisation (one leader $(L,0,1)$, all other agents $(F,0,1)$) and let $R_t$ be the first time the leader has round number $t$. With probability at least $1-n^{-\eta}$, for every round $t<n^a$:
--
--   1. $R_{t+1}<\infty$ and $R_{t+1}-R_t\le D\,n\log_2 n$ interactions;
--   2. there is $s\ge R_t$ with $s+c\,n\log_2 n\le R_{t+1}$ such that at every time $u\in[s,\,s+c\,n\log_2 n]$ every agent has round number $t$.
--
--   This is the clock that organises the MC+ simulation into rounds of $\Theta(\log n)$ time, each with a window in which all agents agree on the round.
--
--   Differences from the source:
--   - reading: 'Starting from the standard phase-clock initialisation with a unique leader' → one agent (L, 0, 1), all others (F, 0, 1); reason: the paper does not spell out the standard initialisation; this is the start state of the clock component (p.22)
--   - reading: 'signals a clock anomaly' → both interacting agents enter an absorbing anomaly state without a round number; reason: the paper does not specify the anomaly states
--   - encoding: D log n and c log n time → D·n·log₂ n and c·n·log₂ n interactions; reason: time = interactions / n
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Theorem 6 and the clock rules, p.19 (PDF p.20), ll.704–716

import Mathlib
import Definitions.Def_PopRAM_PhaseClock

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Theorem 6** with the clock rules (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held
version sha256 f13223b3…, p.19, PDF p.20). "For any fixed constants a, c, η > 0, there exist
constants m and D, depending only on a, c, η, such that the following holds for all sufficiently
large n. Starting from the standard phase-clock initialisation with a unique leader, with
probability at least 1 − n^{−η}, each of the first n^a rounds lasts at most D log n time and contains
an interval of at least c log n time during which all agents have the same round number."

For all `a, c, η > 0` there are a number of phases `m ≥ 1` and `D > 0` (depending only on
`a, c, η`) and `n₀` such that for all `n ≥ n₀` and every leader `a₀`, with probability at least
`1 − n^{-η}` the clock with `m` phases started from the standard initialisation satisfies, for
every round `t < n^a`: round `t + 1` starts (`R_{t+1} < ∞`), `R_{t+1} − R_t ≤ D·n log₂ n`
interactions, and there is `s ≥ R_t` with `s + c·n log₂ n ≤ R_{t+1}` such that at every time `u`
with `s ≤ u ≤ s + c·n log₂ n` every agent has round number `t`. Here `R_t` is the first time the
leader has round number `t`.

**Formalization Note** Round `t` lasts from `R_t` to `R_{t+1}`; times are in interactions.
"Starting from the standard phase-clock initialisation" is read as one agent `(L, 0, 1)` and all
others `(F, 0, 1)`. -/
theorem theorem_6 (a c η : ℝ) (ha : 0 < a) (hc : 0 < c) (hη : 0 < η) :
    ∃ m : ℕ, ∃ D : ℝ, 1 ≤ m ∧ 0 < D ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ a₀ : Fin n,
      sched n {ω | ¬ ∀ t : ℕ, (t : ℝ) < (n : ℝ) ^ a →
          ∃ s₀ s₁ : ℕ, roundTime m a₀ t ω = s₀ ∧ roundTime m a₀ (t + 1) ω = s₁ ∧
            ((s₁ : ℝ) - s₀ ≤ D * n * Real.logb 2 n) ∧
            ∃ s : ℕ, s₀ ≤ s ∧ (s : ℝ) + c * n * Real.logb 2 n ≤ s₁ ∧
              ∀ u : ℕ, s ≤ u → (u : ℝ) ≤ s + c * n * Real.logb 2 n →
                ∀ b, roundOf (run (clockδ m) (clockInit a₀) ω u b) = some t}
        ≤ whpBound n η := by sorry

end PopRAM
