-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_lemma_2_5
-- name    : TurnstileCutSparsify.Main.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:41:05.669305+00:00
-- url     : https://prove2.me/theorems/9db7f17f-9a66-40d7-b715-a2d4e8db0302
-- title:
--   Lemma 2.5 — Freedman's inequality (Tropp's form): one-sided increments d_i ≤ D, uniformly over time
-- statement:
--   Let $(Y_i)_{i\ge0}$ be a real-valued martingale with respect to a filtration $(\mathcal H_i)_{i\ge0}$, with $Y_0=0$, whose differences $d_i=Y_i-Y_{i-1}$ satisfy $d_i\le D$ almost surely for all $i\ge1$, and let $V_i=\sum_{j=1}^i\mathbb E[d_j^2\mid\mathcal H_{j-1}]$ be its predictable quadratic variation. Then for all $z\ge0$ and $v>0$,
--   $$\mathbb P\big(\exists i\ge0:\ Y_i\ge z\ \text{and}\ V_i\le v\big)\le\exp\Big\{-\frac{z^2/2}{v+Dz/3}\Big\}.$$
--   The paper uses it through its fixed-time two-sided consequence (2).
--
--   Differences from the source:
--   - encoding: V_i = Σ_{j≤i} E[d_j² | H_{j−1}] → predQV μ ℱ Y i ∈ [0, ∞]: ⨆_K Σ_{j=1}^{i} μ[min(d_j², K) | ℱ (j−1)], compared with ENNReal.ofReal v; reason: the conditional expectation of a nonnegative variable as an increasing limit; equal to the textbook value, and no square-integrability is added
--   - encoding: martingale with respect to (H_i); Y_0 = 0; d_i ≤ D a.s.; probability P → Mathlib Martingale Y ℱ μ on a probability space; Y 0 = 0; ∀ i ≥ 1, ∀ᵐ ω, Y i ω − Y (i−1) ω ≤ D; μ of the event as an ENNReal; reason: same hypotheses
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Lemma 2.5, p. 10

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Randomness

open scoped BigOperators Classical
open MeasureTheory

namespace TurnstileCutSparsify.Main

/-- **Lemma 2.5** (Freedman's inequality [Tro11, Theorem 1.1]; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 10).
Let `(Y_i)_{i ≥ 0}` be a real-valued martingale with respect to a filtration `(H_i)_{i ≥ 0}`, with
`Y_0 = 0`, whose differences `d_i = Y_i − Y_{i−1}` satisfy `d_i ≤ D` almost surely for all `i ≥ 1`,
and let `V_i = Σ_{j=1}^{i} E[d_j² | H_{j−1}]` (`predQV`, valued in `[0, ∞]`). Then for all `z ≥ 0`
and `v > 0`, `P(∃ i ≥ 0 : Y_i ≥ z and V_i ≤ v) ≤ exp(−(z²/2) / (v + D z / 3))`. -/
theorem lemma_2_5 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (hY : Martingale Y ℱ μ) (hY0 : Y 0 = 0) (D : ℝ)
    (hD : ∀ i, 1 ≤ i → ∀ᵐ ω ∂μ, Y i ω - Y (i - 1) ω ≤ D) (z v : ℝ) (hz : 0 ≤ z) (hv : 0 < v) :
    μ {ω | ∃ i : ℕ, z ≤ Y i ω ∧ predQV μ ℱ Y i ω ≤ ENNReal.ofReal v} ≤
      ENNReal.ofReal (Real.exp (-(z ^ 2 / 2) / (v + D * z / 3))) := by sorry

end TurnstileCutSparsify.Main
