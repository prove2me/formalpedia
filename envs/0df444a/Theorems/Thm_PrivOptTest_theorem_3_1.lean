-- Prove2me | Theorems.Thm_PrivOptTest_theorem_3_1
-- name    : PrivOptTest.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:44.071268+00:00
-- url     : https://prove2.me/theorems/2d02b54e-6129-4edf-b5a2-928706cf2783
-- title:
--   Theorem 3.1, p.14 — lower bound for thresholds
-- statement:
--   There are universal constants $c>0$ and $m_0\in\mathbb N$ such that for every finite $\mathcal X\subset\mathbb R$ with $|\mathcal X|\ge m_0$, every $\varepsilon>0$ and every $t\le n$, every $\varepsilon$-private tester for $\mathcal H_{\mathrm{thr}}$ with resolution $t$ at dataset size $n$ (Definition 1.2) satisfies
--   $$t\ge c\,\frac{\log\log|\mathcal X|}{\varepsilon}.$$
--
--   This is the lower half of Theorem 1.3: interaction cannot beat $\log\log m/\varepsilon$, in contrast with the $O(1/\varepsilon)$ of a trusted curator.
--
--   Differences from the source:
--   - generalization: n, t ∈ ℕ (from 1) → t ≤ n with t = 0 allowed; reason: no tester with resolution 0 exists (completeness and soundness would both hold on a realizable pair), so the case is vacuous; specializes to the source
--   - encoding: testers on multisets → IsTester … (1/10) over protocols on sequences Fin n → X; reason: multiset protocols are a subclass, so the bound over sequences implies it
--   - encoding: log → log₂; reason: any fixed base only rescales c
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 3.1, p.14; Definition 1.2, pp.3–4

import Mathlib
import Definitions.Def_PrivOptTest_IsTester

namespace PrivOptTest

/-- **Theorem 3.1** (Lower bound for thresholds, p.14). There are universal constants `c > 0` and
`m₀ ∈ ℕ` such that for every `m ≥ m₀`, every `X ⊆ ℝ` with `|X| = m`, every `ε > 0` and every `n, t`
with `t ≤ n`, every ε-private tester for `H_thr` with resolution `t` at dataset size `n` (Definition 1.2)
requires `t ≥ c log log m/ε`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 3.1, p.14; Definition 1.2, pp.3–4.

**Formalization Note.** Testers are `IsTester … (1/10)`, Definition 1.2 with probability `0.9`, over all
two-party protocols on sequences `Fin n → X`. `log` is `log₂`; any fixed base changes only `c`. `t = 0`
is allowed: no tester with resolution `0` exists. -/
theorem theorem_3_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ (X : Finset ℝ) (ε : ℝ) (n t : ℕ), m₀ ≤ X.card → 0 < ε → t ≤ n →
      ∀ Pr : Protocol (Fin n → ↥X) Outcome, IsTester Pr (HthrOn X) ε t (1 / 10) →
        c * Real.logb 2 (Real.logb 2 X.card) / ε ≤ t := by sorry

end PrivOptTest
