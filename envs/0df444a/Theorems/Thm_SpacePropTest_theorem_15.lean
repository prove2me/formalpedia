-- Prove2me | Theorems.Thm_SpacePropTest_theorem_15
-- name    : SpacePropTest.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:39.388337+00:00
-- url     : https://prove2.me/theorems/cadffbd9-309e-487b-afa1-793eac35e72a
-- title:
--   Theorem 15, p.17 — a $2^{\tilde O(\sqrt n/\varepsilon^2)}$-state, $2^{\tilde O(\sqrt n/\varepsilon^2)}$-query clock-equipped tester for monotonicity
-- statement:
--   There is an absolute constant $C>0$ such that for every $n\ge1$ and every $\varepsilon\in(0,1]$ there is a clock-equipped tester with at most $B$ states that makes at most $B$ queries, where
--
--   $$B=2^{C\,(\sqrt n/\varepsilon^2)\,\log_2(2n/\varepsilon)^C},$$
--
--   which accepts every monotone $f:\{0,1\}^n\to\{0,1\}$ with probability at least $2/3$ and every $f$ that is $\varepsilon$-far from monotone with probability at most $1/3$.
--
--   With $\log T$ extra bits for the clock this yields the tester of Theorem 14.
--
--   Differences from the source:
--   - reading: clock-equipped algorithm (informal, pp.2–4, 17; formal definition deferred to [CCP+26]) → a $T$-step algorithm with time-indexed query and next-state distributions, a start state, and an output read off the state at time $T$; $S$ states means at most $S$ states, after $K$ queries means $T\le K$; reason: minimal reading of pp.2–4 and 17 (paper.md decision 6); the clock is not counted among the states, as in the paper's conversion to $O(ST)$ states
--   - encoding: $\tilde O(\sqrt n/\varepsilon^2)$ in the exponent → $C\,(\sqrt n/\varepsilon^2)\,\log_2(2n/\varepsilon)^C$ with an absolute $C>0$ chosen before $n$ and $\varepsilon$; reason: standard reading of $\tilde O$; $\log_2(2n/\varepsilon)\ge1$ so the factor never vanishes at $n=1$, $\varepsilon=1$, and for $n\ge2$ it equals $\log(n/\varepsilon)$ up to the constant
--   - reading: “tester for monotonicity” → an $(\varepsilon,1/3)$-tester, for every $\varepsilon\in(0,1]$; reason: §4.1 (p.16) fixes $\delta=1/3$ for a “tester”; $\varepsilon$ appears in the bound, so it is a parameter
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Theorem 15, p.17 (PDF 19)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_ClockAlg

set_option autoImplicit false

namespace SpacePropTest

/-- **Theorem 15** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.17 (PDF 19)).
There is a `2^{Õ(√n/ε²)}`-state, `2^{Õ(√n/ε²)}`-query clock-equipped tester for monotonicity: it
accepts every monotone `f` with probability at least `2/3` and every `f` that is `ε`-far from
monotone with probability at most `1/3`.

**Formalization Note.** `Õ(X)` is `≤ C·X·log₂(2n/ε)^C` with `C` absolute, chosen before `n` and
`ε`; "tester" means an `(ε, 1/3)`-tester (§4.1, p.16), for every `ε ∈ (0, 1]`. -/
theorem theorem_15 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (A : ClockTester n σ),
      (Fintype.card σ : ℝ) ≤ 2 ^ (C * (Real.sqrt n / ε ^ 2) * Real.logb 2 (2 * n / ε) ^ C) ∧
      (A.T : ℝ) ≤ 2 ^ (C * (Real.sqrt n / ε ^ 2) * Real.logb 2 (2 * n / ε) ^ C) ∧
      (∀ f ∈ Mon n, 2 / 3 ≤ A.accProb f) ∧
      (∀ g : BoolFn n, IsFar (Mon n) g ε → A.accProb g ≤ 1 / 3) := by sorry

end SpacePropTest
