-- Prove2me | Theorems.Thm_SpacePropTest_Supplement_theorem_32
-- name    : SpacePropTest.Supplement.theorem_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:44:13.259887+00:00
-- url     : https://prove2.me/theorems/945df01a-cb96-49ef-8b87-6fe21eceddbf
-- title:
--   Theorem 32, p.28 — $k$-juntas are testable with $O(k\log n)$ bits and $n^{O(k)}$ queries
-- statement:
--   There is an absolute constant $C>0$ such that for every $n\ge2$ and every $k$ with $1\le k\le n$:
--
--   1. some $(1/100,1/3)$-tester for the $k$-juntas on $\{0,1\}^n$ has at most $2^{Ck\log_2 n}$ states (so it uses $O(k\log n)$ bits of memory), and
--   2. some clock-equipped tester making $T\le n^{Ck}$ queries, with $|\sigma|$ states and
--   $$|\sigma|\,(T+1)\le2^{Ck\log_2 n},$$
--   accepts every $k$-junta with probability at least $2/3$ and every $g$ that is $1/100$-far from the $k$-juntas with probability at most $1/3$.
--
--   Testers are $M$-state randomized query automata (Definition 7) that run forever and decide by their long-run probability of being in an accepting state; a clock-equipped tester runs for exactly $T$ queries with time-dependent transitions and decides by its final state. This is the upper half of the $k$-junta row of Table 1.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
--   - reading: “tester” (with $\varepsilon$ and $\delta$ not displayed in the theorem) → a $(1/100,1/3)$-tester; reason: §5.2 (p.27) fixes $\varepsilon=0.01$ and $\delta$ “a small constant such as $1/3$” for all remaining upper bounds; $\delta=1/3$ is also the paper's default meaning of “tester” (p.16)
--   - reading: one tester that “uses $O(k\log n)$ bits of memory and makes $n^{O(k)}$ queries” → (a) a Definition 7 tester with at most $2^{C\cdot B}$ states, and (b) a clock-equipped tester making $T$ queries with $|\sigma|\,(T+1)\le2^{C\cdot B}$ (the clock counted in memory) and $T$ within the query bound; reason: Definition 7 testers never halt, so a query count only exists for the finite-query variant of §1.4 (p.3), which has the same space complexity and translates into the infinite-time model; the theorem is used in Table 1 for Definition 7 space complexity, so both are claimed
--   - encoding: $O(k\log n)$ bits, $n^{O(k)}$ queries, for $k\ge1$ → $2^{Ck\log_2 n}$ states, $T\le n^{Ck}$, with one absolute $C>0$ chosen before $n$ and $k$, for $n\ge2$ and $1\le k\le n$; reason: standard reading of $O(\cdot)$ with an absolute constant; small $n$ are absorbed into $C$; Definition 5 takes $k\in[n]$, and the proof gives a constant uniform in $k$; $n\ge2$ keeps $\log_2n\ge1$
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Theorem 32, p.28 (PDF 30); Definition 5, p.15 (PDF 17); §5.2, p.27 (PDF 29); §1.4, p.3 (PDF 5)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester
import Definitions.Def_SpacePropTest_ClockAlg
import Definitions.Def_SpacePropTest_Supplement_Properties

set_option autoImplicit false

namespace SpacePropTest.Supplement

open SpacePropTest

/-- **Theorem 32** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.28 (PDF 30).
Let `k ≥ 1`. There exists a tester for the property of being a `k`-junta that uses `O(k log n)`
bits of memory and makes `n^{O(k)}` queries.

**Formalization Note.** §5.2 (p.27) fixes the distance parameter `ε = 0.01` and the confidence
`δ = 1/3` for all of §5's remaining upper bounds, so "tester" means a `(1/100, 1/3)`-tester.
`O(·)` is read with one absolute constant `C` chosen before `n` and before `k` (uniform in both, as the proof gives); `k` ranges over `[n]` (Definition 5); `log`
is `log₂`, and `n ≥ 2` so that `log₂ n ≥ 1`. The statement has two
conjuncts sharing `C`: (a) a Definition 7 tester (runs forever, decides by its long-run acceptance
probability) with at most `2^{C·B}` states, i.e. `⌈log₂ M⌉ = O(B)` bits; (b) the finite-query
variant of §1.4 (p.3) as a clock-equipped tester making `T` queries, whose memory *including the
clock* is `O(B)` bits (`|σ|·(T+1) ≤ 2^{C·B}`), with `T` within the stated query bound. -/
theorem theorem_32 : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n →
    (∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (A : Tester n σ),
      A.IsTester (Junta n k) (1 / 100) (1 / 3) ∧
      (Fintype.card σ : ℝ) ≤ 2 ^ (C * ((k : ℝ) * Real.logb 2 n))) ∧
    (∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (A : ClockTester n σ),
      (Fintype.card σ : ℝ) * ((A.T : ℝ) + 1) ≤ 2 ^ (C * ((k : ℝ) * Real.logb 2 n)) ∧
      (A.T : ℝ) ≤ (n : ℝ) ^ (C * (k : ℝ)) ∧
      (∀ f ∈ Junta n k, 2 / 3 ≤ A.accProb f) ∧
      (∀ g : BoolFn n, IsFar (Junta n k) g (1 / 100) → A.accProb g ≤ 1 / 3)) := by sorry

end SpacePropTest.Supplement
