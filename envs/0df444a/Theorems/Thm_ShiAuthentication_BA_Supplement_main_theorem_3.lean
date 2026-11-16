-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_main_theorem_3
-- name    : ShiAuthentication.BA.Supplement.main_theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:29:37.743934+00:00
-- url     : https://prove2.me/theorems/8bd49764-18d9-42fb-bdf8-1c95efb1272d
-- title:
--   Main Theorem 3 — authentication complexity of Byzantine broadcast
-- statement:
--   Let $n\ge3$ and $1\le t<n$ with $n\le3t$, and let $A_{BB}(n,t)$ be the minimum number of authentication edges of a public authentication graph on which broadcast from a designated sender $S$ with fault bound $t$ is possible ($+\infty$ if there is none). For every sender:
--
--   1. If $2t<n\le3t$ and $r=n-2t$, then
--   $$\Omega\Big(\frac{n\ln^2(n/r)}{\ln\ln(4n/r)}\Big)\ \le\ A_{BB}(n,t)\ \le\ O\Big(\min\Big\{\frac{n^2}{r}\ln\frac nr,\ n^{3/2}\sqrt{\ln n}\Big\}\Big),$$
--   with absolute constants, uniform over all such $n,t$.
--   2. For every fixed $\alpha\in(1/3,1/2)$, $A_{BB}(n,\lfloor\alpha n\rfloor)=\Theta_\alpha(n)$.
--   3. For every fixed $\alpha\in(1/2,1)$, $A_{BB}(n,\lfloor\alpha n\rfloor)=\Theta_\alpha(n^2)$.
--   4. $A_{BB}(n,t)=o(n^2)$ whenever $t=n/2+o(n)$.
--   5. At maximum resilience, $A_{BB}(n,n-1)=\binom n2-1$.
--
--   In items 2 and 3 the constants and the threshold beyond which the bounds hold may depend on $\alpha$. Item 4 means: for every sequence $t=\tau(n)$ with $(\tau(n)-n/2)/n\to0$ and every $\varepsilon>0$, eventually $A_{BB}(n,\tau(n))\le\varepsilon n^2$.
--
--   The theorem maps the setup cost of designated-sender broadcast across the whole range of fault fractions: linear below $1/2$, superlinear but subquadratic around $1/2$, quadratic above $1/2$, and exactly $\binom n2-1$ at $t=n-1$. It separates broadcast from agreement, which needs a complete PKI already at $n=2t+1$.
--
--   Differences from the source:
--   - encoding: A_BB(n, t) → ABB t S, stated for every designated sender S; reason: Definition 3.3 minimizes over setups for broadcast from a designated sender; the bound is claimed for every sender
--   - encoding: values of A_T(n, t) in ℕ ∪ {+∞} → ℕ∞, compared with real bounds after the cast ℕ∞ → ℝ≥0∞ and ENNReal.ofReal; reason: +∞ is the infimum of the empty family (Definition 3.3); an upper bound in ℝ≥0∞ also asserts finiteness
--   - encoding: Ω(·) ≤ A_BB(n, t) ≤ O(·) for 2t < n ≤ 3t → ∃ c C > 0 before ∀ n t r S, with ofReal(c · f) ≤ A_BB and A_BB ≤ ofReal(C · g); reason: Ω and O range over n and t; uniform constants
--   - encoding: A_BB(n, ⌊αn⌋) = Θ_α(n) (resp. Θ_α(n²)) for fixed α → ∀ α in the interval, ∃ c C > 0, ∃ N₀, ∀ n ≥ N₀, ∀ S, c n ≤ A_BB(n, ⌊αn⌋) ≤ C n (resp. n²); reason: Θ_α is asymptotic in n with constants depending on α; the threshold makes n ≥ 3 and n ≤ 3⌊αn⌋ hold
--   - encoding: A_BB(n, t) = o(n²) whenever t = n/2 + o(n) → ∀ τ : ℕ → ℕ with (τ n − n/2)/n → 0, ∀ ε > 0, eventually ∀ S, A_BB(n, τ n) ≤ ε n²; reason: the standard meaning of the two little-o symbols; every admissible sequence is covered
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Main Theorem 3, pp. 3–4; proof p. 35

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace ShiAuthentication.BA.Supplement

/-- **Main Theorem 3 (Authentication complexity of Byzantine broadcast)**, pp. 3–4, proved p. 35.
Let `n ≥ 3` and `1 ≤ t < n` with `n ≤ 3t`; `A_BB` is taken for every designated sender `S`.
(1) If `2t < n ≤ 3t` and `r = n − 2t`, then
`Ω(n ln²(n/r) / ln ln(4n/r)) ≤ A_BB(n, t) ≤ O(min{(n²/r) ln(n/r), n^{3/2} √(ln n)})`, with absolute
constants uniform over all such `n, t, S`.
(2) For every fixed `α ∈ (1/3, 1/2)`, `A_BB(n, ⌊αn⌋) = Θ_α(n)`.
(3) For every fixed `α ∈ (1/2, 1)`, `A_BB(n, ⌊αn⌋) = Θ_α(n²)`.
(4) `A_BB(n, t) = o(n²)` whenever `t = n/2 + o(n)`.
(5) `A_BB(n, n − 1) = C(n, 2) − 1`. -/
theorem main_theorem_3 :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n t r : ℕ) (S : Fin n), 3 ≤ n → 1 ≤ t → 2 * t < n →
      n ≤ 3 * t → r = n - 2 * t →
      ENNReal.ofReal (c * ((n : ℝ) * Real.log ((n : ℝ) / r) ^ 2 /
          Real.log (Real.log (4 * (n : ℝ) / r)))) ≤ (ABB t S : ℝ≥0∞) ∧
      (ABB t S : ℝ≥0∞) ≤ ENNReal.ofReal (C * min ((n : ℝ) ^ 2 / r * Real.log ((n : ℝ) / r))
          ((n : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (Real.log n)))) ∧
    (∀ α : ℝ, 1 / 3 < α → α < 1 / 2 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ S : Fin n, ENNReal.ofReal (c * n) ≤ (ABB ⌊α * n⌋₊ S : ℝ≥0∞) ∧
        (ABB ⌊α * n⌋₊ S : ℝ≥0∞) ≤ ENNReal.ofReal (C * n)) ∧
    (∀ α : ℝ, 1 / 2 < α → α < 1 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ S : Fin n, ENNReal.ofReal (c * (n : ℝ) ^ 2) ≤ (ABB ⌊α * n⌋₊ S : ℝ≥0∞) ∧
        (ABB ⌊α * n⌋₊ S : ℝ≥0∞) ≤ ENNReal.ofReal (C * (n : ℝ) ^ 2)) ∧
    (∀ τ : ℕ → ℕ, Tendsto (fun n : ℕ => ((τ n : ℝ) - (n : ℝ) / 2) / n) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Fin n,
        (ABB (τ n) S : ℝ≥0∞) ≤ ENNReal.ofReal (ε * (n : ℝ) ^ 2)) ∧
    (∀ n : ℕ, 3 ≤ n → ∀ S : Fin n, ABB (n - 1) S = ((n.choose 2 - 1 : ℕ) : ℕ∞)) := by sorry

end ShiAuthentication.BA.Supplement
