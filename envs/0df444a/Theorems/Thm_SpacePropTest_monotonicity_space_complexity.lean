-- Prove2me | Theorems.Thm_SpacePropTest_monotonicity_space_complexity
-- name    : SpacePropTest.monotonicity_space_complexity
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:32.908489+00:00
-- url     : https://prove2.me/theorems/19feed62-d14d-4f3a-9c33-d20dd64c9073
-- title:
--   Main Theorem, monotonicity row of Table 1 — space complexity $\tilde\Theta(\sqrt n)$ (Theorem 14 and Theorem 41)
-- statement:
--   The monotonicity row of the Main Theorem (Table 1, p.3): testing monotonicity of $f:\{0,1\}^n\to\{0,1\}$ with bounded memory needs $\tilde\Theta(\sqrt n)$ bits. Precisely:
--
--   1. **(Theorem 14)** There is an absolute $C>0$ such that for every $n\ge1$ and every $\varepsilon\in(0,1]$ some $(\varepsilon,1/3)$-tester for monotonicity has at most
--   $$2^{C\,(\sqrt n/\varepsilon^2)\,\log_2(2n/\varepsilon)^C}$$
--   states.
--   2. **(Theorem 41)** There are $\varepsilon\in(0,1]$, $c>0$ and $n_0$ such that for every $n\ge n_0$, every $(\varepsilon,1/3)$-tester for monotonicity with $M$ states has $\lceil\log_2M\rceil\ge c\sqrt n$.
--
--   Testers are $M$-state randomized query automata (Definition 7) that run forever and decide by their long-run probability of being in an accepting state.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
--   - encoding: $\tilde O(\sqrt n/\varepsilon^2)$ in the exponent → $C\,(\sqrt n/\varepsilon^2)\,\log_2(2n/\varepsilon)^C$ with an absolute $C>0$ chosen before $n$ and $\varepsilon$; reason: standard reading of $\tilde O$; $\log_2(2n/\varepsilon)\ge1$ so the factor never vanishes at $n=1$, $\varepsilon=1$, and for $n\ge2$ it equals $\log(n/\varepsilon)$ up to the constant
--   - reading: “tester for monotonicity” → an $(\varepsilon,1/3)$-tester, for every $\varepsilon\in(0,1]$; reason: §4.1 (p.16) fixes $\delta=1/3$ for a “tester”; $\varepsilon$ appears in the bound, so it is a parameter
--   - encoding: “must use $\Omega(\sqrt n)$ bits of space”, for a constant $\varepsilon>0$ → there are $\varepsilon\in(0,1]$, $c>0$ and $n_0$, chosen before $n$, such that for every $n\ge n_0$ every $(\varepsilon,1/3)$-tester with $M$ states has $\lceil\log_2M\rceil\ge c\sqrt n$; reason: standard reading of $\Omega(\cdot)$; $\varepsilon\le1$ is the range of the tester definition (p.16)
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Main Theorem and Table 1, p.3 (PDF 5); Theorem 14, p.17 (PDF 19); Theorem 41, p.36 (PDF 38)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester

set_option autoImplicit false

namespace SpacePropTest

/-- **Main Theorem, monotonicity row of Table 1: `Θ̃(√n)` (Theorem 14 and Theorem 41)**
(C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space Complexity of Property
Testing*, manuscript of November 2, 2026, sha256 65850aa6…; Main Theorem and Table 1, p.3 (PDF 5);
Theorem 14, p.17 (PDF 19); Theorem 41, p.36 (PDF 38)).

1. (Theorem 14) There is an absolute `C > 0` such that for every `n ≥ 1` and every
   `ε ∈ (0, 1]` some tester with at most `2^{C (√n/ε²) log₂(2n/ε)^C}` states is an
   `(ε, 1/3)`-tester for monotonicity.
2. (Theorem 41) There are `ε ∈ (0, 1]`, `c > 0` and `n₀` such that for every `n ≥ n₀` every
   `(ε, 1/3)`-tester for monotonicity, with any number `M` of states, has `⌈log₂ M⌉ ≥ c√n`.

**Formalization Note.** Testers are those of Definition 7 (p.15) with acceptance by long-run
probability (p.16); `Õ` and `Ω` are read with absolute constants quantified before `n`. -/
theorem monotonicity_space_complexity :
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (A : Tester n σ),
        A.IsTester (Mon n) ε (1 / 3) ∧
        (Fintype.card σ : ℝ) ≤
          2 ^ (C * (Real.sqrt n / ε ^ 2) * Real.logb 2 (2 * n / ε) ^ C)) ∧
    (∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (A : Tester n σ),
        A.IsTester (Mon n) ε (1 / 3) → c * Real.sqrt n ≤ (bits (Fintype.card σ) : ℝ)) := by sorry

end SpacePropTest
