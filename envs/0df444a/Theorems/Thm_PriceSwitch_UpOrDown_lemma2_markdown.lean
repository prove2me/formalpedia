-- Prove2me | Theorems.Thm_PriceSwitch_UpOrDown_lemma2_markdown
-- name    : PriceSwitch.UpOrDown.lemma2_markdown
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:04:05.822325+00:00
-- url     : https://prove2.me/theorems/37a0bf17-3c63-49e9-8d08-f1d7c783003d
-- title:
--   Lemma 2, case (i), p. 1379 — y_n = inf{s ≥ 0 : G(n,s) = 0} is strictly increasing and G changes sign once, − to +
-- statement:
--   Consider the markdown case (i) for a pair of prices: $0 < b < a$, $0 < \lambda_a < \lambda_b$ and $a\lambda_a < b\lambda_b$. Let
--
--   $$
--   G(n,t) = a\lambda_a - b\lambda_b - b(\lambda_a - \lambda_b)P(N_b(t) \ge n), \qquad y_n = \inf\{s \ge 0 : G(n,s) = 0\}.
--   $$
--
--   Then:
--   1. for every $n \ge 1$, $G(n,\cdot)$ has a zero on $[0,\infty)$, so $y_n$ is well defined;
--   2. $y_1 > 0$, and the sequence $(y_n)_{n \ge 1}$ is strictly increasing; in particular it is bounded away from zero;
--   3. $G(n,\cdot)$ has a single sign change, from $-$ to $+$: $G(n,s) < 0$ for $0 \le s < y_n$ and $G(n,s) > 0$ for $s > y_n$.
--
--   In §5 this is applied to $G^1(n,t) = r - r_1 - p_1(\lambda - \lambda_1)P(N_1(t) \ge n)$, i.e. to the pair $(p, p_1)$, which is in case (i). The proof of Theorem 3 uses it at its first step: $L^1(1,t) = G^1(1,t)$ has a unique sign change from $-$ to $+$ at $x_1$.
--
--   **Formalization Note** The page says the sequence is "bounded and strictly increasing". It is not bounded: for fixed $t$, $G(n,t) \to a\lambda_a - b\lambda_b < 0$ as $n \to \infty$, so $y_n \to \infty$. What the paper uses (proof of Corollary 1, p. 1380) is that it is bounded away from zero, which is what is stated here ($y_1 > 0$ together with monotonicity). The infimum is Lean's `sInf`, and item 1 guarantees the set is nonempty.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Lemma 2, p. 1379

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.UpOrDown

/-- Feng–Gallego (1995), Lemma 2, case (i), p. 1379. The printed word "bounded" is corrected to
bounded away from zero: the thresholds tend to infinity. -/
theorem lemma2_markdown (a la b lb : ℝ) (hpair : PriceSwitch.Markdown.IsMarkdownPair a la b lb) :
    let y : ℕ → ℝ := fun n => sInf {s : ℝ | 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0}
    (∀ n, 1 ≤ n → ∃ s, 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0) ∧
    0 < y 1 ∧
    StrictMonoOn y (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → ∀ s, 0 ≤ s → s < y n → PriceSwitch.Markdown.G a la b lb n s < 0) ∧
    (∀ n, 1 ≤ n → ∀ s, y n < s → 0 < PriceSwitch.Markdown.G a la b lb n s) := by sorry

end PriceSwitch.UpOrDown
