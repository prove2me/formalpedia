-- Prove2me | Theorems.Thm_PrivOptTest_Supplement_theorem_4_1
-- name    : PrivOptTest.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:35:34.234201+00:00
-- url     : https://prove2.me/theorems/85b04864-5562-47b2-9873-8769d8a03f8b
-- title:
--   Theorem 4.1, p.27 — lower bound $t\ge c\,d\log(m/d)/\varepsilon$ for private halfspace testing
-- statement:
--   There are universal constants $c,C_0,\varepsilon_0>0$ and $d_0\in\mathbb N$ such that the following holds. For all $d,m\in\mathbb N$ with $d\ge d_0$ and $m\ge C_0d$ there is a public domain $\mathcal X_{d,m}\subseteq\mathbb R^d$ with $|\mathcal X_{d,m}|=m$ such that for every $0<\varepsilon\le\varepsilon_0$, every integer
--   $$n\ge C_0\,\frac{m\,d\log(m/d)}{\varepsilon}$$
--   and every resolution $t\in[n]$, every $\varepsilon$-private tester for $\mathcal H_{\mathrm{hs}}$ at dataset size $n$ over $\mathcal X_{d,m}$ (success probability $0.9$, Definition 1.2) satisfies
--   $$t\ge c\,\frac{d\log(m/d)}{\varepsilon}.$$
--   The domain depends only on $(d,m)$: it is chosen before $\varepsilon$, $n$ and $t$.
--
--   Compared with the $\Theta(\log\log m/\varepsilon)$ resolution for thresholds, the dependence on the domain size is exponentially larger, and the resolution grows at least linearly in the dimension.
--
--   **Formalization Note** $\log$ is the natural logarithm; it sits under the existential constants.
--
--   Differences from the source:
--   - encoding: universal constants c, C, C₀, ε₀ > 0 → c, C₀, ε₀ > 0 (C omitted); reason: C does not occur in the statement
--   - encoding: testers on multisets → IsTester … (1/10) over protocols on sequences Fin n → X; reason: multiset protocols are a subclass, so the bound over sequences implies it
--   - encoding: log (base unstated) → Real.log; reason: any fixed base only rescales c and C₀
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 4.1, p.27; Definition 1.2, pp.3–4

import Mathlib
import Definitions.Def_PrivOptTest_IsTester
import Definitions.Def_PrivOptTest_Supplement_HhsOn

namespace PrivOptTest

namespace Supplement

/-- **Theorem 4.1** (Lower bound for halfspaces, arXiv:2611.03599, manuscript sha256 4ac94dcf…, p.27).
There are universal constants `c, C₀, ε₀ > 0` and `d₀ ∈ ℕ` such that for every `d ≥ d₀` and
`m ≥ C₀ d` there is a public domain `X_{d,m} ⊆ ℝ^d` with `|X_{d,m}| = m` such that for every
`0 < ε ≤ ε₀`, every integer `n ≥ C₀ m d log(m/d)/ε` and every `t ∈ [n]`, every ε-private tester for
`H_hs` (Definition 1.2, success probability 0.9) at dataset size `n` over `X_{d,m}` with resolution `t`
has `t ≥ c d log(m/d)/ε`. The domain is chosen from `(d, m)` alone, before `ε`, `n`, `t`.

**Formalization Note.** `log` is the natural logarithm; it sits under the existential `c` and `C₀`, so
the base changes only the constants. The paper also lists a constant `C`, which does not occur in the
statement and is dropped. Testers are the base mission's `IsTester` at `β = 1/10`, on sequences
`Fin n → X`. -/
theorem theorem_4_1 :
    ∃ c C₀ ε₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < ε₀ ∧ ∃ d₀ : ℕ, ∀ d m : ℕ, d₀ ≤ d → C₀ * d ≤ m →
      ∃ X : Finset (EuclideanSpace ℝ (Fin d)), X.card = m ∧
        ∀ (ε : ℝ) (n t : ℕ) (Pr : Protocol (Fin n → ↥X) Outcome),
          0 < ε → ε ≤ ε₀ → C₀ * ((m : ℝ) * d * Real.log ((m : ℝ) / d)) / ε ≤ n →
          1 ≤ t → t ≤ n → IsTester Pr (HhsOn X) ε t (1 / 10) →
          c * (d * Real.log ((m : ℝ) / d)) / ε ≤ t := by sorry

end Supplement

end PrivOptTest
