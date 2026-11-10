-- Prove2me | Theorems.Thm_TwoConnSS_theorem_5_1_comparison
-- name    : TwoConnSS.theorem_5_1_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:44:04.599206+00:00
-- url     : https://prove2.me/theorems/7e99da60-88cc-40c8-9d4b-5010d39ed9f6
-- title:
--   Proof of Theorem 5.1 — the weighted comparison $\min\{|F_A|,|F_{B,1}|,|F_{B,2}|\}\le\frac{1040}{833}\,\mathrm{opt}$
-- statement:
--   Let $m_4, m_{\ne 4}, m_4^{\mathrm{merged}}, \mathrm{opt}, a, b_1, b_2$ be natural numbers with $|S_0| = m_4 + m_{\ne4} > 0$, $m_4^{\mathrm{merged}} \le m_4$, $|S_0| \le \mathrm{opt}$, and
--   $$a \le \tfrac54 m_4 + \tfrac{16}{13} m_{\ne4} - 2,\quad b_1 \le \tfrac65 m_4^{\mathrm{merged}} + \tfrac54 (m_4 - m_4^{\mathrm{merged}}) + \tfrac{67}{50} m_{\ne4} - 2,\quad b_2 \le \mathrm{opt} + m_4^{\mathrm{merged}} + m_{\ne4} - 1.$$
--   With $x = m_{\ne4}/|S_0|$ and $y = m_4^{\mathrm{merged}}/|S_0|$:
--
--   1. $\dfrac{\min\{a, b_1, b_2\}}{\mathrm{opt}} \le \min\Big\{\tfrac54 - \tfrac{x}{52},\ \tfrac54 + \tfrac{9x}{100} - \tfrac{y}{20},\ 1 + x + y\Big\}$;
--   2. $\tfrac{728}{833}\big(\tfrac54 - \tfrac{x}{52}\big) + \tfrac{100}{833}\big(\tfrac54 + \tfrac{9x}{100} - \tfrac{y}{20}\big) + \tfrac{5}{833}(1 + x + y) = \tfrac{1040}{833}$ for all $x, y$;
--   3. $\min\{a, b_1, b_2\} \le \tfrac{1040}{833}\,\mathrm{opt}$.
--
--   With $a = |F_A|$, $b_1 = |F_{B,1}|$, $b_2 = |F_{B,2}|$ the hypotheses are (23), (29), (30) and $|S_0| \le \mathrm{opt}_E(G)$, and the conclusion is the ratio of Theorem 5.1.
--
--   Differences from the source:
--   - reading: the comparison applied to |F_A|, |F_{B,1}|, |F_{B,2}|, opt_E(G) and the counts of S₀ → a statement about arbitrary natural numbers satisfying (23), (29), (30) and |S₀| ≤ opt; reason: the step is pure arithmetic once these bounds are known; the solutions enter only through them
--   - encoding: real ratios → rational arithmetic; reason: all quantities are rational
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), proof of Theorem 5.1, p.72 (PDF p.73)

import Mathlib

namespace TwoConnSS

/-- **The final comparison in the proof of Theorem 5.1.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), proof of Theorem 5.1, p.72: "Our
exact initial-cover construction gives |S0| ≤ opt(G). Set x := m≠4/|S0|, y := m4^merged/|S0|.
Theorem 8.29, specifically (23), together with (29) and (30) give, after dropping negative constants,
min{|FA|, |FB,1|, |FB,2|}/opt(G) ≤ min{5/4 − x/52, 5/4 + 9x/100 − y/20, 1 + x + y}. Weight these
three expressions by 728/833, 100/833, and 5/833, respectively. The coefficients of both x and y
vanish, and the weighted average is 1040/833."

Let `m₄, m_{≠4}, m₄^merged, opt, a, b₁, b₂` be natural numbers with `|S₀| = m₄ + m_{≠4} > 0`,
`m₄^merged ≤ m₄`, `|S₀| ≤ opt`, and
- (23) `a ≤ (5/4)m₄ + (16/13)m_{≠4} − 2`,
- (29) `b₁ ≤ (6/5)m₄^merged + (5/4)(m₄ − m₄^merged) + (67/50)m_{≠4} − 2`,
- (30) `b₂ ≤ opt + m₄^merged + m_{≠4} − 1`.

With `x = m_{≠4}/|S₀|`, `y = m₄^merged/|S₀|`:
1. `min{a, b₁, b₂}/opt ≤ min{5/4 − x/52, 5/4 + 9x/100 − y/20, 1 + x + y}`;
2. for all real `x, y`, `(728/833)(5/4 − x/52) + (100/833)(5/4 + 9x/100 − y/20) + (5/833)(1 + x + y)
   = 1040/833`;
3. `min{a, b₁, b₂} ≤ (1040/833)·opt`.

**Formalization Note.** `a, b₁, b₂` stand for `|F_A|, |F_{B,1}|, |F_{B,2}|` and `opt` for
`opt_E(G)`; the hypotheses are (23), (29), (30) and `|S₀| ≤ opt`. Arithmetic is in `ℚ`. -/
theorem theorem_5_1_comparison (m4 mNe4 mMerged opt a b₁ b₂ : ℕ) (hS₀ : 0 < m4 + mNe4)
    (hmerged : mMerged ≤ m4) (hopt : m4 + mNe4 ≤ opt)
    (ha : (a : ℚ) ≤ 5 / 4 * m4 + 16 / 13 * mNe4 - 2)
    (hb₁ : (b₁ : ℚ) ≤ 6 / 5 * mMerged + 5 / 4 * ((m4 : ℚ) - mMerged) + 67 / 50 * mNe4 - 2)
    (hb₂ : (b₂ : ℚ) ≤ opt + mMerged + mNe4 - 1) :
    (let x : ℚ := (mNe4 : ℚ) / ((m4 + mNe4 : ℕ) : ℚ)
     let y : ℚ := (mMerged : ℚ) / ((m4 + mNe4 : ℕ) : ℚ)
     ((min (min a b₁) b₂ : ℕ) : ℚ) / (opt : ℚ) ≤
       min (min (5 / 4 - x / 52) (5 / 4 + 9 * x / 100 - y / 20)) (1 + x + y)) ∧
    (∀ x y : ℚ, 728 / 833 * (5 / 4 - x / 52) + 100 / 833 * (5 / 4 + 9 * x / 100 - y / 20) +
      5 / 833 * (1 + x + y) = 1040 / 833) ∧
    ((min (min a b₁) b₂ : ℕ) : ℚ) ≤ 1040 / 833 * (opt : ℚ) := by sorry

end TwoConnSS
