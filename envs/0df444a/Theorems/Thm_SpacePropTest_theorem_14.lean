-- Prove2me | Theorems.Thm_SpacePropTest_theorem_14
-- name    : SpacePropTest.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:58.941777+00:00
-- url     : https://prove2.me/theorems/fd5581b5-87d4-40a3-9169-c359b5a90daf
-- title:
--   Theorem 14, p.17 — a $2^{\tilde O(\sqrt n/\varepsilon^2)}$-state tester for monotonicity
-- statement:
--   There is an absolute constant $C>0$ such that for every $n\ge1$ and every $\varepsilon\in(0,1]$ there is a tester $A$ (Definition 7) with at most
--
--   $$2^{C\,(\sqrt n/\varepsilon^2)\,\log_2(2n/\varepsilon)^C}$$
--
--   states that is an $(\varepsilon,1/3)$-tester for monotonicity: $\hat p_{A_f}(S_{\mathrm{Acc}})\ge2/3$ for every monotone $f:\{0,1\}^n\to\{0,1\}$ and $\hat p_{A_g}(S_{\mathrm{Acc}})\le1/3$ for every $g$ that is $\varepsilon$-far from monotone.
--
--   In bits of memory this is $\tilde O(\sqrt n/\varepsilon^2)$, the upper half of the monotonicity row of Table 1.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
--   - encoding: $\tilde O(\sqrt n/\varepsilon^2)$ in the exponent → $C\,(\sqrt n/\varepsilon^2)\,\log_2(2n/\varepsilon)^C$ with an absolute $C>0$ chosen before $n$ and $\varepsilon$; reason: standard reading of $\tilde O$; $\log_2(2n/\varepsilon)\ge1$ so the factor never vanishes at $n=1$, $\varepsilon=1$, and for $n\ge2$ it equals $\log(n/\varepsilon)$ up to the constant
--   - reading: “tester for monotonicity” → an $(\varepsilon,1/3)$-tester, for every $\varepsilon\in(0,1]$; reason: §4.1 (p.16) fixes $\delta=1/3$ for a “tester”; $\varepsilon$ appears in the bound, so it is a parameter
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Theorem 14, p.17 (PDF 19)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester

set_option autoImplicit false

namespace SpacePropTest

/-- **Theorem 14** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.17 (PDF 19)).
There is a `2^{Õ(√n/ε²)}`-state tester for monotonicity.

**Formalization Note.** `Õ(X)` is `≤ C·X·log₂(2n/ε)^C` with `C` absolute, chosen before `n` and
`ε`; "tester" is an `(ε, 1/3)`-tester of Definition 7 (§4.1, p.16), for every `ε ∈ (0, 1]`. -/
theorem theorem_14 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (A : Tester n σ),
      A.IsTester (Mon n) ε (1 / 3) ∧
      (Fintype.card σ : ℝ) ≤
        2 ^ (C * (Real.sqrt n / ε ^ 2) * Real.logb 2 (2 * n / ε) ^ C) := by sorry

end SpacePropTest
