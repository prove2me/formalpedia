-- Prove2me | Theorems.Thm_SpacePropTest_theorem_41
-- name    : SpacePropTest.theorem_41
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:10.423864+00:00
-- url     : https://prove2.me/theorems/138ede47-af13-4495-85a9-2678a611c65e
-- title:
--   Theorem 41, p.36 — for some constant $\varepsilon>0$, every $(\varepsilon,1/3)$-tester for monotonicity uses $\Omega(\sqrt n)$ bits
-- statement:
--   There are constants $\varepsilon\in(0,1]$, $c>0$ and $n_0$ such that for every $n\ge n_0$, every $(\varepsilon,1/3)$-tester for monotonicity of Boolean functions on $\{0,1\}^n$ (Definition 7, any number $M$ of states, not necessarily in normal form) uses
--
--   $$\lceil\log_2M\rceil\ge c\sqrt n$$
--
--   bits of memory.
--
--   This is the lower half of the monotonicity row of Table 1; with Theorem 14 it pins the space complexity at $\tilde\Theta(\sqrt n)$ for constant $\varepsilon$.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
--   - encoding: “must use $\Omega(\sqrt n)$ bits of space”, for a constant $\varepsilon>0$ → there are $\varepsilon\in(0,1]$, $c>0$ and $n_0$, chosen before $n$, such that for every $n\ge n_0$ every $(\varepsilon,1/3)$-tester with $M$ states has $\lceil\log_2M\rceil\ge c\sqrt n$; reason: standard reading of $\Omega(\cdot)$; $\varepsilon\le1$ is the range of the tester definition (p.16)
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Theorem 41, p.36 (PDF 38)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester

set_option autoImplicit false

namespace SpacePropTest

/-- **Theorem 41** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.36 (PDF 38)).
There exists a constant `ε > 0` such that any `(ε, 1/3)`-tester for monotonicity must use
`Ω(√n)` bits of space.

**Formalization Note.** `Ω(√n)` bits: there are `c > 0` and `n₀`, chosen with `ε` before
`n`, such that every `(ε, 1/3)`-tester (Definition 7, any number `M` of states, no normal-form
assumption) for the monotone functions on `{0,1}ⁿ`, `n ≥ n₀`, has `⌈log₂ M⌉ ≥ c√n`. -/
theorem theorem_41 :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (A : Tester n σ),
        A.IsTester (Mon n) ε (1 / 3) → c * Real.sqrt n ≤ (bits (Fintype.card σ) : ℝ) := by sorry

end SpacePropTest
