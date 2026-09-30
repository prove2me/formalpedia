-- Prove2me | Theorems.Thm_SabanisEuler_Rate_one_step_increment
-- name    : SabanisEuler.Rate.one_step_increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T23:18:34.181991+00:00
-- url     : https://prove2.me/theorems/19114681-18e2-4a8e-a45b-181415e181f1
-- title:
--   Lemma 4 — one-step increments of the scheme are of order $n^{-1/2}$ in $L^p$
-- statement:
--   For every $n\ge1$ let $X_n$ solve the scheme (2.2) on $[0,T]$ with coefficients $b_n,\sigma_n$. Suppose A-2 and A-4–A-6 hold (with exponent $l$ in A-6), that B-2 holds with $\alpha=1/2$, and that B-3 holds. Let $l\le p_0-2$ and $0<p\le\max\big(2,\frac{2p_0}{l+2}\big)$. Then there is a positive constant $C$, independent of $n$, such that for every $n\ge1$
--   $$\sup_{0\le t\le T}\mathbb E|X_n(t)-X_n(\kappa_n(t))|^p\le Cn^{-p/2}.$$
--
--   The scheme freezes its coefficients at the last grid point $\kappa_n(t)=\lfloor nt\rfloor/n$; the lemma says that the process moves only by $O(n^{-1/2})$ in $L^p$ between grid points, which is the second error source of the main theorem.
--
--   **Formalization Note** Hypothesis B-3 is added to the printed hypotheses. The printed proof bounds the increment by $n^{-p/2}$ times moments of $X_n$ that must be uniform in $n$ (Lemma 2), and those rest on B-3; in the paper's application (Model 2) B-3 holds (Remark 5). Expectations and the supremum are computed in $[0,\infty]$.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 16, Lemma 4, eq. (4.3)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_SabanisEuler_Shared_Conditions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.Rate

open EthierKurtz

/-- Sabanis (2016), arXiv:1308.1796v4, p. 16, Lemma 4, eq. (4.3): for the scheme (2.2) under
A-2, A-4–A-6 and B-2 with `α = 1/2`, for every `0 < p ≤ max(2, 2p₀/(l + 2))` and
`l ≤ p₀ - 2`, there is a positive constant `C` independent of `n` with
`sup_{0 ≤ t ≤ T} 𝔼|Xₙ(t) - Xₙ(κₙ(t))|^p ≤ C n^{-p/2}` for every `n ≥ 1`.
**Added hypothesis:** B-3 (`hB3`). The printed proof bounds the increment through moments
of `Xₙ` that are uniform in `n` (Lemma 2), which rest on B-3; B-2 alone gives moment
bounds growing with `n`. In the paper's application (Model 2) B-3 holds (Remark 5). -/
theorem one_step_increment
    {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState d₁) (hW : IsWienerMartingale P ℱ W)
    (T : ℝ≥0) (hT : 0 < T)
    (p₀ p₁ : ℝ) (hp₀ : 2 ≤ p₀) (hp₁ : 2 ≤ p₁)
    (b : ℝ≥0 × SDEState d → SDEState d) (σ : ℝ≥0 × SDEState d → Diffusion d d₁)
    (hb : Measurable b) (hσ : Measurable σ)
    (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d) (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁)
    (hbₙ : ∀ n : ℕ, 1 ≤ n → Measurable (bₙ n)) (hσₙ : ∀ n : ℕ, 1 ≤ n → Measurable (σₙ n))
    (ξ : Ω → SDEState d) (hξ : Measurable[ℱ 0] ξ)
    (l : ℝ)
    (hA2 : CondA2 T b) (hA4 : CondA4 T p₀ b σ) (hA5 : CondA5 P p₀ ξ)
    (hA6 : CondA6 T p₁ l b σ)
    (hB2 : CondB2 T (1 / 2) b σ bₙ σₙ)
    (hB3 : CondB3 T p₀ bₙ σₙ)
    (hl : l ≤ p₀ - 2)
    (p : ℝ) (hp : 0 < p) (hpmax : p ≤ max 2 (2 * p₀ / (l + 2)))
    (Xₙ : ℕ → ℝ≥0 → Ω → SDEState d)
    (hXₙ : ∀ n : ℕ, 1 ≤ n → IsSchemeSolution P ℱ W T ξ bₙ σₙ n (Xₙ n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ∫⁻ ω, ‖Xₙ n t ω - Xₙ n (kappa n t) ω‖ₑ ^ p ∂P)
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(p / 2))) := by sorry

end SabanisEuler.Rate
