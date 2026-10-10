-- Prove2me | Theorems.Thm_RandomListsMatching_GeneralRates_chord_lower_bound
-- name    : RandomListsMatching.GeneralRates.chord_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:39.938929+00:00
-- url     : https://prove2.me/theorems/f16f7154-bc14-4fe3-a366-24bf9ca28fae
-- title:
--   §5.4, p. 15 display — Σ g(f, m_{a,a₁}) ≥ (s_a/β_a) g(f, β_a) by concavity of g and g(f, 0) = 0
-- statement:
--   Let $g$ be the function of Claim 2 (with $h$ as there). Let $f \le 1$ and let $m_1, \dots, m_k \ge 0$ be reals whose maximum $\beta = m_{j_0}$ satisfies $0 < \beta \le f$. With $s = \sum_j m_j$,
--   $$
--   \sum_{j=1}^k g(f, m_j) \;\ge\; \sum_{j=1}^k \frac{m_j}{\beta}\, g(f, \beta) \;=\; \frac{s}{\beta}\, g(f, \beta).
--   $$
--
--   This is the display of p. 15 of Jaillet and Lu with $m_j = m_{a,a_1}$, $\beta = \beta_a = \max_{a_1} m_{a,a_1}$ and $s = s_a$; it replaces the sum of $g$-values by a function of $s_a$ and $\beta_a$ alone.
--
--   **Formalization Note** $\beta$ is required positive, so that $s/\beta$ is a genuine quotient; the page's $\beta_a$ is the maximum of the $m_{a,a_1}$, stated through `hmax`. The bound $\beta \le f$ is the paper's $s_a \ge \beta_a$ together with $f_a \ge s_a$, and keeps every $m_j$ in the interval $[0, f]$ on which Claim 3 gives concavity.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 15, display after "Furthermore, because g is concave in the second argument and g(f_a, 0) = 0"

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

namespace RandomListsMatching.GeneralRates

theorem chord_lower_bound (f : ℝ) (hf1 : f ≤ 1) {k : ℕ} (m : Fin k → ℝ) (j₀ : Fin k)
    (hm : ∀ j, 0 ≤ m j) (hmax : ∀ j, m j ≤ m j₀) (hβ : 0 < m j₀) (hβf : m j₀ ≤ f) :
    (∑ j, m j) / m j₀ * g f (m j₀) ≤ ∑ j, g f (m j) := by sorry

end RandomListsMatching.GeneralRates
