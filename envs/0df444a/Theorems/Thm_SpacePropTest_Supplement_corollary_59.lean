-- Prove2me | Theorems.Thm_SpacePropTest_Supplement_corollary_59
-- name    : SpacePropTest.Supplement.corollary_59
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:46:52.818712+00:00
-- url     : https://prove2.me/theorems/c5850a57-d634-4524-9db4-e3987310821f
-- title:
--   Corollary 59, p.46 — every $(1/10,1/3)$-tester for linear threshold functions uses $\Omega(\log n)$ bits
-- statement:
--   There are constants $c>0$ and $n_0$ such that for every $n\ge n_0$, every $(1/10,1/3)$-tester for the linear threshold functions on $\{0,1\}^n$ with $M$ states uses
--   $$\lceil\log_2M\rceil\ge c\log_2 n$$
--   bits of memory.
--
--   Testers are $M$-state randomized query automata (Definition 7), with any number of states and not necessarily in normal form, that run forever and decide by their long-run probability of being in an accepting state. With Theorem 33 this gives the $\Theta(\log n)$ LTF row of Table 1.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
--   - encoding: “requires $\Omega(\log n)$ bits of memory” → there are $c>0$ and $n_0$, chosen before $n$, with $\lceil\log_2M\rceil\ge c\log_2n$ for all $n\ge n_0$; reason: standard reading of $\Omega(\cdot)$; memory is $\lceil\log_2M\rceil$ bits (p.16)
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Corollary 59, p.46 (PDF 48)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester
import Definitions.Def_SpacePropTest_Supplement_Properties

set_option autoImplicit false

namespace SpacePropTest.Supplement

open SpacePropTest

/-- **Corollary 59** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.46 (PDF 48)).
Every `(1/10, 1/3)`-tester for LTFs requires `Ω(log n)` bits of memory.

**Formalization Note.** `Ω(log n)`: there are `c > 0` and `n₀`, chosen before `n`, such that every
`(1/10, 1/3)`-tester for the linear threshold functions on `{0,1}ⁿ` (Definition 6, 0/1 cube, real
weights), `n ≥ n₀`, has `⌈log₂ M⌉ ≥ c·log₂ n`. The bound holds for every Definition 7 tester (any
number `M` of states, any finite state type, no normal-form assumption); bits are `⌈log₂ M⌉`. -/
theorem corollary_59 : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (A : Tester n σ),
      A.IsTester (LTF n) (1 / 10) (1 / 3) →
        c * Real.logb 2 n ≤ (bits (Fintype.card σ) : ℝ) := by sorry

end SpacePropTest.Supplement
