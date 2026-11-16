-- Prove2me | Theorems.Thm_SpacePropTest_Supplement_theorem_57
-- name    : SpacePropTest.Supplement.theorem_57
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:46:29.316124+00:00
-- url     : https://prove2.me/theorems/c9b20bc5-145f-457a-a50d-d3c1e93bdf77
-- title:
--   Theorem 57, p.45 — for $k(n)\le n^{0.99}$, every $(1/10,1/3)$-tester for $k$-juntas uses $\Omega(k\log n)$ bits
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $k:\mathbb N\to\mathbb N$ satisfy $1\le k(n)\le n^{0.99}$ for all sufficiently large $n$. Then there is $n_0$ such that for every $n\ge n_0$, every $(1/10,1/3)$-tester for the $k(n)$-juntas on $\{0,1\}^n$ with $M$ states uses
--   $$\lceil\log_2M\rceil\ge c\,k(n)\log_2 n$$
--   bits of memory.
--
--   Testers are $M$-state randomized query automata (Definition 7), with any number of states and not necessarily in normal form, that run forever and decide by their long-run probability of being in an accepting state. With Theorem 32 this gives the $\Theta(k\log n)$ junta row of Table 1.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
--   - reading: “must use at least $\Omega(k\log n)$ bits of space” for a function $k$ with $1\le k(n)\le n^{0.99}$ eventually → there is $c>0$, chosen before $k$, such that for every such $k$ there is $n_0$ with $\lceil\log_2M\rceil\ge c\,k(n)\log_2n$ for all $n\ge n_0$; reason: the stronger of the two readings of where $\Omega$'s constant sits (it does not depend on $k$), which is what the proof gives (log B ≥ 0.01 k log n, p.45); $n_0$ depends on $k$ because the hypothesis on $k$ is only eventual
--   - encoding: $n^{0.99}$ → the real power $n^{99/100}$; reason: same number
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Theorem 57, p.45 (PDF 47)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester
import Definitions.Def_SpacePropTest_Supplement_Properties

set_option autoImplicit false

namespace SpacePropTest.Supplement

open SpacePropTest

/-- **Theorem 57** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.45 (PDF 47).
Let `k : ℕ → ℕ` satisfy `1 ≤ k(n) ≤ n^{0.99}` for all sufficiently large `n`. Every
`(1/10, 1/3)`-tester for `k`-juntas must use at least `Ω(k log n)` bits of space.

**Formalization Note.** `Ω(k log n)`: there is an absolute `c > 0`, chosen before `k`, such that for every such `k`
there is `n₀` (which may depend on `k`, since the hypothesis on `k` is only eventual) with: for
every `n ≥ n₀`, every `(1/10, 1/3)`-tester for the `k(n)`-juntas on `{0,1}ⁿ` has
`⌈log₂ M⌉ ≥ c·k(n)·log₂ n`. `0.99` is the real exponent `99/100`. The bound holds for every Definition 7 tester (any number `M` of
states, any finite state type, no normal-form assumption); bits are `⌈log₂ M⌉`. -/
theorem theorem_57 : ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ → ℕ,
    (∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → 1 ≤ k n ∧ (k n : ℝ) ≤ (n : ℝ) ^ ((99 : ℝ) / 100)) →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (A : Tester n σ),
        A.IsTester (Junta n (k n)) (1 / 10) (1 / 3) →
          c * (k n : ℝ) * Real.logb 2 n ≤ (bits (Fintype.card σ) : ℝ) := by sorry

end SpacePropTest.Supplement
