-- Prove2me | Theorems.Thm_SabanisEuler_UniformRate_one_step_increment
-- name    : SabanisEuler.UniformRate.one_step_increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T04:00:22.439728+00:00
-- url     : https://prove2.me/theorems/4a5801b8-e2b5-412c-9057-f781b192be8c
-- title:
--   Lemma 4 — the one-step increment of the scheme is of order n^{-p/2} in L^p
-- statement:
--   In the setting of the scheme (2.2) on $[0,T]$ (Wiener martingale $W$, right-continuous filtration, $p_0,p_1\ge2$, Borel coefficients, $\mathcal F_0$-measurable initial value $X(0)$), let $(X_n)_{n\ge1}$ solve (2.2) with coefficients $b_n,\sigma_n$ and let $\kappa_n(t)=\lfloor nt\rfloor/n$. Suppose A-2, A-4, A-5, A-6 (with exponent $l$), B-2 with $\alpha=1/2$, and B-3 hold, and $l\le p_0-2$. Then for every $p$ with
--   $$0<p\le\max\Big(2,\frac{2p_0}{l+2}\Big)$$
--   there is a positive constant $C$ independent of $n$ such that for every $n\ge1$,
--   $$\sup_{0\le t\le T}\mathbb E|X_n(t)-X_n(\kappa_n(t))|^p\le Cn^{-p/2}.$$
--
--   The estimate says that between two grid points the scheme moves by $O(n^{-1/2})$ in $L^p$, uniformly in time; it feeds the error term of the Itô-formula argument for Theorem 3.
--
--   **Formalization Note** B-3 is added to the printed hypotheses (A-2, A-4–A-6, B-2 with $\alpha=1/2$). The printed proof bounds the increment by $n^{-p/2}\,\mathbb E(1+|X_n(\kappa_n(r))|^{l+2})^{p/2}$, which is $O(n^{-p/2})$ only with moments of $X_n$ bounded uniformly in $n$ (Lemma 2), and Lemma 2 needs B-3; B-2 alone gives moment bounds that may grow with $n$. In the paper's application (Model 2), B-3 holds (Remark 5). Expectations and the supremum are computed in $[0,\infty]$.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 16, Lemma 4, eq. (4.3)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_SabanisEuler_Shared_Conditions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.UniformRate

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

end SabanisEuler.UniformRate
