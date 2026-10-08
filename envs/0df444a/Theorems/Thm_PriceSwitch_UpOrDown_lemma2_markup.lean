-- Prove2me | Theorems.Thm_PriceSwitch_UpOrDown_lemma2_markup
-- name    : PriceSwitch.UpOrDown.lemma2_markup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:08.657961+00:00
-- url     : https://prove2.me/theorems/5874eb38-40f9-4970-8b93-16d2225e4600
-- title:
--   Lemma 2, case (ii), p. 1379 — y_n = inf{s ≥ 0 : G(n,s) = 0} is strictly increasing and G changes sign once, + to −
-- statement:
--   Consider the markup case (ii) for a pair of prices: $0 < a < b$, $0 < \lambda_b < \lambda_a$ and $b\lambda_b < a\lambda_a$. Let
--
--   $$
--   G(n,t) = a\lambda_a - b\lambda_b - b(\lambda_a - \lambda_b)P(N_b(t) \ge n), \qquad y_n = \inf\{s \ge 0 : G(n,s) = 0\}.
--   $$
--
--   Then:
--   1. for every $n \ge 1$, $G(n,\cdot)$ has a zero on $[0,\infty)$, so $y_n$ is well defined;
--   2. $y_1 > 0$, and the sequence $(y_n)_{n \ge 1}$ is strictly increasing; in particular it is bounded away from zero;
--   3. $G(n,\cdot)$ has a single sign change, from $+$ to $-$: $G(n,s) > 0$ for $0 \le s < y_n$ and $G(n,s) < 0$ for $s > y_n$.
--
--   In §5 this is applied to $G^2(n,t) = r - r_2 - p_2(\lambda - \lambda_2)P(N_2(t) \ge n)$, i.e. to the pair $(p, p_2)$, which is in case (ii). The proof of Theorem 3 uses that $G^2(n+1,t) > G^2(n,t)$ and that $G^2$ is decreasing in $t$ to locate $z_n$.
--
--   **Formalization Note** The page says the sequence is "bounded and strictly increasing". It is not bounded: for fixed $t$, $G(n,t) \to a\lambda_a - b\lambda_b > 0$ as $n \to \infty$, so $y_n \to \infty$. What the paper uses is that it is bounded away from zero, which is what is stated here ($y_1 > 0$ together with monotonicity). The infimum is Lean's `sInf`, and item 1 guarantees the set is nonempty.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Lemma 2, p. 1379

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.UpOrDown

/-- Feng–Gallego (1995), Lemma 2, case (ii), p. 1379. The printed word "bounded" is corrected to
bounded away from zero: the thresholds tend to infinity. -/
theorem lemma2_markup (a la b lb : ℝ) (hpair : PriceSwitch.Markdown.IsMarkupPair a la b lb) :
    let y : ℕ → ℝ := fun n => sInf {s : ℝ | 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0}
    (∀ n, 1 ≤ n → ∃ s, 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0) ∧
    0 < y 1 ∧
    StrictMonoOn y (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → ∀ s, 0 ≤ s → s < y n → 0 < PriceSwitch.Markdown.G a la b lb n s) ∧
    (∀ n, 1 ≤ n → ∀ s, y n < s → PriceSwitch.Markdown.G a la b lb n s < 0) := by sorry

end PriceSwitch.UpOrDown
