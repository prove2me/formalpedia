-- Prove2me | Theorems.Thm_PrivOptTest_Supplement_theorem_4_11
-- name    : PrivOptTest.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:37:47.235172+00:00
-- url     : https://prove2.me/theorems/c2343f4a-7eba-4f6d-ac35-33dd882def01
-- title:
--   Theorem 4.11, p.34 — a non-interactive $\varepsilon$-private halfspace tester once $t\ge C(n^2d\log(2m)/\varepsilon)^{1/3}$
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Fix $d\ge1$, $m,n\in\mathbb N$ and $\varepsilon\in(0,1]$. For every public domain $\mathcal X\subseteq\mathbb R^d$ with $|\mathcal X|=m$ and every $t\in[n]$ with
--   $$t\ge C\Big(\frac{n^2\,d\log(2m)}{\varepsilon}\Big)^{1/3}\tag{15}$$
--   there is a non-interactive, randomized, $\varepsilon$-two-party differentially private tester for $\mathcal H_{\mathrm{hs}}$ with resolution $t$ (success probability $0.9$, Definition 1.2).
--
--   The bound is a weighted geometric mean of $n$ and $d\log(2m)/\varepsilon$, and gives a better dependence on the dimension than Theorem 4.7 at moderate dataset sizes.
--
--   **Formalization Note** $\log$ is natural; it sits under $C$. The cube root is the real power $1/3$.
--
--   Differences from the source:
--   - encoding: non-interactive → IsNonInteractive: Alice speaks at round 0, Bob's round-1 message ignores hers, the run stops at round 2 with an output computed from the public coins and the two messages; reason: each party sends one message from its own data, private coins and public coins, and the output is a function of the releases (pp.33–34, 51–53)
--   - encoding: log (base unstated) → Real.log; reason: any fixed base only rescales C
--   - encoding: testers on multisets → IsTester … over protocols on sequences Fin n → X; reason: a sequence tester becomes an order-invariant (multiset) one when each party first permutes its records with a uniform permutation from its private coins; privacy, soundness and completeness are preserved, so the two existence claims are equivalent
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 4.11, p.34; proof pp.52–53

import Mathlib
import Definitions.Def_PrivOptTest_IsTester
import Definitions.Def_PrivOptTest_Supplement_HhsOn
import Definitions.Def_PrivOptTest_Supplement_IsNonInteractive

namespace PrivOptTest

namespace Supplement

/-- **Theorem 4.11** (Halfspace testing via the BLR net mechanism, arXiv:2611.03599, manuscript sha256
4ac94dcf…, p.34). There is a universal constant `C > 0` such that for every `d ≥ 1`, `m, n ∈ ℕ`,
`ε ∈ (0, 1]`, every public `X ⊆ ℝ^d` with `|X| = m` and every `t ∈ [n]` with
`t ≥ C (n² d log(2m)/ε)^{1/3}` (15), there is a non-interactive, randomized, ε-two-party DP tester
(Definition 1.2, success probability 0.9) for `H_hs` with resolution `t`.

**Formalization Note.** `log` is natural; it sits under `C`. The cube root is the real power `1/3` of a
nonnegative number. -/
theorem theorem_4_11 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n : ℕ) (ε : ℝ) (X : Finset (EuclideanSpace ℝ (Fin d))) (t : ℕ),
      1 ≤ d → 0 < ε → ε ≤ 1 → 1 ≤ t → t ≤ n →
      C * (((n : ℝ) ^ 2 * d * Real.log (2 * X.card)) / ε) ^ ((1 : ℝ) / 3) ≤ t →
      ∃ Pr : Protocol (Fin n → ↥X) Outcome,
        IsNonInteractive Pr ∧ IsTester Pr (HhsOn X) ε t (1 / 10) := by sorry

end Supplement

end PrivOptTest
