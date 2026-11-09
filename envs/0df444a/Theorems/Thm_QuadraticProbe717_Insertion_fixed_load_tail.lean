-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_fixed_load_tail
-- name    : QuadraticProbe717.Insertion.fixed_load_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:03.958207+00:00
-- url     : https://prove2.me/theorems/33af1f68-3374-4a22-914f-8738394dcc2c
-- title:
--   Proposition 6.1 — all three fixed-load tail regimes
-- statement:
--   There is an absolute constant $B>0$ such that for every $\eta>0$ there are $A_\eta>0$ and $n_0(\eta)$ with the following property. For every prime $n\ge n_0(\eta)$, every fixed completion order and every integer load $m<n$, put $\varepsilon=1-m/n$. Suppose $1/\sqrt{\log n}<\varepsilon\le1/2$, and let $T_m$ be the actual next insertion cost. Then all three bounds hold:
--   $$\Pr[T_m>k]\le\frac{A_\eta k^\eta}{\varepsilon^2k^2}\quad(\varepsilon^{-1}<k\le\sqrt n),$$
--   $$\Pr[T_m>\lceil n^{19/25}\rceil]\le\frac{B}{\varepsilon^2n},$$
--   $$\Pr[T_m>k]\le\frac{3\ln(\varepsilon^{-1})}{k}\quad(\varepsilon n\le k\le n/2).$$
--   All thresholds $k$ are integers. The first bound retains every positive exponent slack; the second constant is absolute, and the third retains the exact coefficient three.
--
--   Differences from the source:
--   - encoding: m=(1−ε)n keys → integer m<n and ε=1−m/n; reason: exactly the attainable loads, without rounding m or requiring exact half-load
--   - encoding: distinct keys with independent uniform hashes and arbitrary fixed offset completion → insertion-time indices, ZMod n slots, every fixed completion permutation, and exact finite averages; reason: key labels do not affect insertion; repeated quadratic probes and the first empty slot are retained
--   - reading: k^{o(1)}, an absolute O in (8b), and sufficiently large n → B absolute before η, then Aη and n₀(η), all before n,m,ε,k and completion order; reason: uniform subpolynomial quantification; a common threshold may be enlarged to the largest of the three thresholds
--   - encoding: k=ceil(n^0.76) and source regime endpoints → natural ceiling of the real power n^(19/25), k≤sqrt n, and 2k≤n; reason: 0.76=19/25 exactly; integer comparisons encode the floors without changing attainable endpoints
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Proposition 6.1, equations (8a), (8b), (8c), p. 11 (PDF p. 11)

import Definitions.Def_QuadraticProbe717_Insertion_laws
import Definitions.Def_QuadraticProbe717_Insertion_arithmetic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem fixed_load_tail :
    ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ,
      ∀ (n : ℕ) [NeZero n], n₀ ≤ n → n.Prime →
      ∀ (π : Equiv.Perm (ZMod n)) (m : ℕ), m < n →
      let ε := vacancyFraction n m
      1 / Real.sqrt (Real.log n) < ε → ε ≤ 1 / 2 →
        (∀ k : ℕ, ε⁻¹ < k → (k : ℝ) ≤ Real.sqrt n →
          fixedTail n m π k ≤ A * (k : ℝ)^η / (ε^2 * (k : ℝ)^2)) ∧
        fixedTail n m π ⌈(n : ℝ) ^ (19 / 25 : ℝ)⌉₊ ≤ B / (ε^2 * n) ∧
        (∀ k : ℕ, ε * n ≤ k → 2 * k ≤ n →
          fixedTail n m π k ≤ 3 * Real.log ε⁻¹ / k) := by sorry

end QuadraticProbe717.Insertion
