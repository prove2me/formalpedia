-- Prove2me | Theorems.Thm_PrivOptTest_Supplement_theorem_E_4
-- name    : PrivOptTest.Supplement.theorem_E_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:38:17.731466+00:00
-- url     : https://prove2.me/theorems/736272a9-cf28-404b-8562-92d4c969661c
-- title:
--   Theorem E.4, p.50 — lower bounds for private halfspace testing as a function of the sample size
-- statement:
--   There are universal constants $c>0$, $N_0\ge1$, $C_0\ge1$, $d_0\in\mathbb N$ and $\varepsilon_0>0$ such that the following holds. For all $d\ge d_0$ and $m\ge C_0d$ there is a public domain $\mathcal X_{d,m}\subseteq\mathbb R^d$ with $|\mathcal X_{d,m}|=m$, chosen from $(d,m)$ alone, such that for every $0<\varepsilon\le\varepsilon_0$ and every $n\in\mathbb N$ with $n\varepsilon\ge N_0$, every $\varepsilon$-private tester for $\mathcal H_{\mathrm{hs}}$ over $\mathcal X_{d,m}$ with resolution $t\in[2n]$ at dataset size $n$ (success probability $0.9$, Definition 1.2) satisfies
--   $$t\ \ge\ c\cdot\begin{cases}\sqrt{n/\varepsilon}, & N_0\le n\varepsilon\le d^2,\\[2pt] \dfrac d\varepsilon\,\log\Big(2+\min\Big\{\dfrac md,\dfrac{n\varepsilon}{d^2}\Big\}\Big), & n\varepsilon>d^2.\end{cases}\tag{24}$$
--   Logarithms are to base $2$.
--
--   This extends Theorem 4.1 to all dataset sizes: the bound reaches $\Omega(d\log(m/d)/\varepsilon)$ once $n\varepsilon\gtrsim md$, and the two cases agree up to constants at $n\varepsilon\asymp d^2$.
--
--   Differences from the source:
--   - reading: “let X_{d,m} be the domain of Lemma E.3” → ∃ X with X.card = m, quantified after d, m and before ε, n, t; reason: Lemma E.3 itself asserts the existence of a domain of size m depending only on (d, m), and Theorem 1.4 (p.5) states the bound in this form; the domain's construction is proof content
--   - encoding: resolution t (Definition 1.2) → 1 ≤ t ≤ 2n; reason: Definition 1.2’s range t ∈ [2n]
--   - encoding: testers on multisets → IsTester … (1/10) over protocols on sequences Fin n → X; reason: multiset protocols are a subclass, so the bound over sequences implies it
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem E.4, p.50; Lemma E.3, p.49; Definition 1.2, pp.3–4

import Mathlib
import Definitions.Def_PrivOptTest_IsTester
import Definitions.Def_PrivOptTest_Supplement_HhsOn

namespace PrivOptTest

namespace Supplement

/-- **Theorem E.4** (Lower bounds as a function of the sample size, arXiv:2611.03599, manuscript sha256
4ac94dcf…, p.50; Lemma E.3, p.49). There are universal constants `c > 0`, `N₀ ≥ 1`, `C₀ ≥ 1`, `d₀ ∈ ℕ`
and `ε₀ > 0` such that for every `d ≥ d₀` and `m ≥ C₀ d` there is a public domain `X_{d,m} ⊆ ℝ^d` with
`|X_{d,m}| = m`, chosen from `(d, m)` alone, such that for every `0 < ε ≤ ε₀`, every `n ∈ ℕ` with
`nε ≥ N₀` and every resolution `t ∈ [2n]`, every ε-private tester (Definition 1.2, success probability
0.9) for `H_hs` over `X_{d,m}` with resolution `t` at dataset size `n` has (24):
`t ≥ c √(n/ε)` if `N₀ ≤ nε ≤ d²`, and `t ≥ c (d/ε) log(2 + min{m/d, nε/d²})` if `nε > d²`.

**Formalization Note.** The domain of Lemma E.3 enters through what that lemma asserts of it: it has
exactly `m` points and depends only on `(d, m)`. Logarithms are to base 2, as §E says (p.48); the base
changes only `c`. `t ∈ [2n]` is Definition 1.2's range. -/
theorem theorem_E_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ d₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ d m : ℕ, d₀ ≤ d → C₀ * d ≤ m →
      ∃ X : Finset (EuclideanSpace ℝ (Fin d)), X.card = m ∧
        ∀ (ε : ℝ) (n t : ℕ) (Pr : Protocol (Fin n → ↥X) Outcome),
          0 < ε → ε ≤ ε₀ → N₀ ≤ n * ε → 1 ≤ t → t ≤ 2 * n →
          IsTester Pr (HhsOn X) ε t (1 / 10) →
          ((n : ℝ) * ε ≤ (d : ℝ) ^ 2 → c * Real.sqrt (n / ε) ≤ t) ∧
          ((d : ℝ) ^ 2 < n * ε →
            c * ((d : ℝ) / ε) * Real.logb 2 (2 + min ((m : ℝ) / d) ((n : ℝ) * ε / (d : ℝ) ^ 2)) ≤ t) := by sorry

end Supplement

end PrivOptTest
