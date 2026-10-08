-- Prove2me | Theorems.Thm_PriceSwitch_UpOrDown_lemma3_markup
-- name    : PriceSwitch.UpOrDown.lemma3_markup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:04:38.58599+00:00
-- url     : https://prove2.me/theorems/83a83e30-658a-4229-a102-15dab0c8fb0d
-- title:
--   Lemma 3, case (ii), p. 1382 — Δ(n,t) = J(n,t;t) − J(n,t;0) changes sign once at t_n, t_n strictly increasing, Δ ↓ (a−b)n
-- statement:
--   Consider the markup case (ii) for a pair of prices: $0 < a < b$, $0 < \lambda_b < \lambda_a$ and $b\lambda_b < a\lambda_a$. Let $J(n,t;s)$ be the expected revenue of charging $a$ for $s$ time units and $b$ afterwards, and let
--
--   $$
--   \Delta(n,t) = J(n,t;t) - J(n,t;0), \qquad t_n = \inf\{t > 0 : \Delta(n,t) = 0\}.
--   $$
--
--   Then for every $n \ge 1$:
--   1. $\Delta(n,\cdot)$ is continuous and has a zero on $(0,\infty)$;
--   2. it has a unique sign change on $\{t > 0\}$ at $t_n$: $\Delta(n,t) > 0$ for $0 < t < t_n$ and $\Delta(n,t) < 0$ for $t > t_n$;
--   3. the sequence $(t_n)_{n \ge 1}$ is strictly increasing;
--   4. on $t > t_n$, $\Delta(n,t)$ is monotone decreasing, and $\Delta(n,t) \to (a - b)n$ as $t \to \infty$.
--
--   In §5 this is applied twice: to $\Delta^2$ with the pair $(p, p_2)$, and to $\Delta = J^1(\cdot;0) - J^2(\cdot;0)$ with the pair $(p_1, p_2)$, both in case (ii).
--
--   **Formalization Note** The page proves Lemma 3 for case (i) only and states that "the proof for case (ii) is entirely analogous" (p. 1390); the statement here is the lemma's case (ii) as printed. The limit $(p_1 - p_2)n$ of the page is $(a - b)n$ in the generic pair. Continuity is stated on all of $\mathbb R$.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Lemma 3, p. 1382 (case (ii): "entirely analogous", Appendix, p. 1390)

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.UpOrDown

open Filter Topology

/-- Feng–Gallego (1995), Lemma 3, case (ii), p. 1382, for `Δ(n, t) = J(n, t; t) − J(n, t; 0)` and
`t_n = inf{t > 0 : Δ(n, t) = 0}`. -/
theorem lemma3_markup (a la b lb : ℝ) (hpair : PriceSwitch.Markdown.IsMarkupPair a la b lb) :
    let Δ : ℕ → ℝ → ℝ := fun n t => PriceSwitch.Markdown.switchRevenue a la b lb n t t - PriceSwitch.Markdown.switchRevenue a la b lb n t 0
    let tn : ℕ → ℝ := fun n => sInf {t : ℝ | 0 < t ∧ Δ n t = 0}
    (∀ n, 1 ≤ n → Continuous (Δ n)) ∧
    (∀ n, 1 ≤ n → ∃ t, 0 < t ∧ Δ n t = 0) ∧
    (∀ n, 1 ≤ n → ∀ t, 0 < t → t < tn n → 0 < Δ n t) ∧
    (∀ n, 1 ≤ n → ∀ t, tn n < t → Δ n t < 0) ∧
    StrictMonoOn tn (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → AntitoneOn (Δ n) (Set.Ioi (tn n))) ∧
    (∀ n, 1 ≤ n → Tendsto (Δ n) atTop (𝓝 ((a - b) * n))) := by sorry

end PriceSwitch.UpOrDown
