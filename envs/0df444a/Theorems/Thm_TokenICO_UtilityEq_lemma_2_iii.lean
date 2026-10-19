-- Prove2me | Theorems.Thm_TokenICO_UtilityEq_lemma_2_iii
-- name    : TokenICO.UtilityEq.lemma_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:53.313574+00:00
-- url     : https://prove2.me/theorems/3199f056-1f35-4f8f-820d-1933c07beaca
-- title:
--   Lemma 2(iii) — the largest zero of speculator utility
-- statement:
--   Fix a positive ICO price $\tau$. If the set of positive sales levels $s\le m$ at which speculator utility $u_\tau(s)$ is zero has a greatest element $s_0(\tau)$, then
--
--   $$s_0(\tau)<m(1-c/v),\qquad s>s_0(\tau),\ s\le m\Longrightarrow u_\tau(s)<0.$$
--
--   The largest participation threshold therefore lies below the fraction at which the firm would abandon production.
--
--   **Formalization Note** As in Lemma 2(ii), the price must be positive: at zero price, utility vanishes for all feasible sales levels. The greatest-element condition includes existence.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), p. 12, Lemma 2(iii)

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- Lemma 2(iii), p. 12: the largest positive zero of speculator profit
lies below the misconduct threshold, after which profit is negative. -/
theorem lemma_2_iii (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f') (Qr : ℝ → ℝ → ℝ)
    (hQr : ProdOptimal m c v μ Qr) (τ s0 : ℝ)
    (hτ : 0 < τ)
    (hs0 : IsGreatest {s : ℝ | 0 < s ∧ s ≤ m ∧ u m v z μ Qr τ s = 0} s0) :
    s0 < m * (1 - c / v) ∧
    ∀ s : ℝ, s0 < s → s ≤ m → u m v z μ Qr τ s < 0 := by sorry

end TokenICO.UtilityEq
