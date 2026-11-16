-- Prove2me | Theorems.Thm_SpacePropTest_Supplement_theorem_42
-- name    : SpacePropTest.Supplement.theorem_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:46:02.62727+00:00
-- url     : https://prove2.me/theorems/797fcd71-2f02-40cf-8f38-db0aedd6cd4a
-- title:
--   Theorem 42, p.39 — every $(1/100,1/3)$-tester for linearity uses $\Omega(n)$ bits
-- statement:
--   There are constants $c>0$ and $n_0$ such that for every $n\ge n_0$, every $(1/100,1/3)$-tester for the linear (parity) functions on $\{0,1\}^n$ with $M$ states uses
--   $$\lceil\log_2M\rceil\ge c\,n$$
--   bits of memory.
--
--   Testers are $M$-state randomized query automata (Definition 7), with any number of states and not necessarily in normal form, that run forever and decide by their long-run probability of being in an accepting state. With Theorem 30 this gives the $\Theta(n)$ linearity row of Table 1: the BLR test's memory is optimal up to a constant factor.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
--   - encoding: “must use $\Omega(n)$ bits of space” → there are $c>0$ and $n_0$, chosen before $n$, with $\lceil\log_2M\rceil\ge cn$ for all $n\ge n_0$; reason: standard reading of $\Omega(\cdot)$
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Theorem 42, p.39 (PDF 41)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester
import Definitions.Def_SpacePropTest_Supplement_Properties

set_option autoImplicit false

namespace SpacePropTest.Supplement

open SpacePropTest

/-- **Theorem 42** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.39 (PDF 41).
Any `(1/100, 1/3)`-tester for linearity must use `Ω(n)` bits of space.

**Formalization Note.** `Ω(n)`: there are `c > 0` and `n₀`, chosen before `n`, such that every `(1/100, 1/3)`-tester
for the linear functions on `{0,1}ⁿ`, `n ≥ n₀`, has `⌈log₂ M⌉ ≥ c·n`. The bound holds for every Definition 7 tester (any number `M` of
states, any finite state type, no normal-form assumption); bits are `⌈log₂ M⌉`. -/
theorem theorem_42 : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (A : Tester n σ),
      A.IsTester (Lin n) (1 / 100) (1 / 3) →
        c * (n : ℝ) ≤ (bits (Fintype.card σ) : ℝ) := by sorry

end SpacePropTest.Supplement
