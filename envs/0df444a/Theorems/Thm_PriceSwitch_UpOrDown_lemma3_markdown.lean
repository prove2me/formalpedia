-- Prove2me | Theorems.Thm_PriceSwitch_UpOrDown_lemma3_markdown
-- name    : PriceSwitch.UpOrDown.lemma3_markdown
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:04:29.169178+00:00
-- url     : https://prove2.me/theorems/0365029a-f32b-48a0-9c01-18807e937297
-- title:
--   Lemma 3, case (i), p. 1382 — Δ(n,t) = J(n,t;t) − J(n,t;0) changes sign once at t_n, t_n strictly increasing, Δ ↑ (a−b)n
-- statement:
--   Consider the markdown case (i) for a pair of prices: $0 < b < a$, $0 < \lambda_a < \lambda_b$ and $a\lambda_a < b\lambda_b$. Let $J(n,t;s)$ be the expected revenue of charging $a$ for $s$ time units and $b$ afterwards, and let
--
--   $$
--   \Delta(n,t) = J(n,t;t) - J(n,t;0), \qquad t_n = \inf\{t > 0 : \Delta(n,t) = 0\},
--   $$
--
--   the difference between never switching and switching at once. Then for every $n \ge 1$:
--   1. $\Delta(n,\cdot)$ is continuous and has a zero on $(0,\infty)$;
--   2. it has a unique sign change on $\{t > 0\}$ at $t_n$: $\Delta(n,t) < 0$ for $0 < t < t_n$ and $\Delta(n,t) > 0$ for $t > t_n$;
--   3. the sequence $(t_n)_{n \ge 1}$ is strictly increasing;
--   4. on $t > t_n$, $\Delta(n,t)$ is monotone increasing, and $\Delta(n,t) \to (a - b)n$ as $t \to \infty$.
--
--   In §5 this is applied to $\Delta^1$, with the pair $(p, p_1)$. "By repeatedly applying Lemma 3" the paper obtains the unique sign changes at $t^1_n$, $t^2_n$, $t_n$ that define the thresholds of Theorem 3.
--
--   **Formalization Note** The page writes the limit as $(p_1 - p_2)n$ in the two-price notation of §4, where $p_1$ is the initial and $p_2$ the second price; here these are $a$ and $b$. Continuity is stated on all of $\mathbb R$ (the Poisson means are read as $0$ for negative time), which contains the page's claim for $t \ge 0$.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Lemma 3, p. 1382 (proof: Appendix, pp. 1390–1391)

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.UpOrDown

open Filter Topology

/-- Feng–Gallego (1995), Lemma 3, case (i), p. 1382, for `Δ(n, t) = J(n, t; t) − J(n, t; 0)` and
`t_n = inf{t > 0 : Δ(n, t) = 0}`. -/
theorem lemma3_markdown (a la b lb : ℝ) (hpair : PriceSwitch.Markdown.IsMarkdownPair a la b lb) :
    let Δ : ℕ → ℝ → ℝ := fun n t => PriceSwitch.Markdown.switchRevenue a la b lb n t t - PriceSwitch.Markdown.switchRevenue a la b lb n t 0
    let tn : ℕ → ℝ := fun n => sInf {t : ℝ | 0 < t ∧ Δ n t = 0}
    (∀ n, 1 ≤ n → Continuous (Δ n)) ∧
    (∀ n, 1 ≤ n → ∃ t, 0 < t ∧ Δ n t = 0) ∧
    (∀ n, 1 ≤ n → ∀ t, 0 < t → t < tn n → Δ n t < 0) ∧
    (∀ n, 1 ≤ n → ∀ t, tn n < t → 0 < Δ n t) ∧
    StrictMonoOn tn (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → MonotoneOn (Δ n) (Set.Ioi (tn n))) ∧
    (∀ n, 1 ≤ n → Tendsto (Δ n) atTop (𝓝 ((a - b) * n))) := by sorry

end PriceSwitch.UpOrDown
