-- Prove2me | Theorems.Thm_SabanisEuler_Rate_moment_bounds
-- name    : SabanisEuler.Rate.moment_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T23:03:23.422746+00:00
-- url     : https://prove2.me/theorems/d50eac29-f744-46ec-b870-7a8345dd7ec9
-- title:
--   Lemma 2 — uniform moment bounds for the SDE and the scheme
-- statement:
--   Let $X$ solve the SDE (2.1) and, for every $n\ge1$, let $X_n$ solve the scheme (2.2) on $[0,T]$ with coefficients $b_n,\sigma_n$ and the same initial value $X(0)$ and Wiener martingale $W$. Suppose that A-1–A-5 hold, that B-2 holds with some $\alpha\in(0,1/2]$, and that B-3 holds. Then for every $0<p\le p_0$,
--   $$\sup_{0\le t\le T}\mathbb E|X(t)|^p<\infty\qquad\text{and}\qquad\sup_{n\ge1}\sup_{0\le t\le T}\mathbb E|X_n(t)|^p<\infty.$$
--
--   This is the moment control that every rate estimate of the paper rests on: the moments of the tamed scheme stay bounded uniformly in the step size although the coefficients grow superlinearly.
--
--   **Formalization Note** Expectations and suprema are computed in $[0,\infty]$ and finiteness is stated as $<\infty$. The paper names the constant $C:=C(p,T,K,\mathbb E[|X(0)|^p])$; only its independence of $n$ is formalized. The exponent is taken positive ($p>0$, the paper's $\mathcal L^p$ convention).
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 8, Lemma 2, eq. (3.4)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_SabanisEuler_Shared_Conditions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.Rate

open EthierKurtz

/-- Sabanis (2016), arXiv:1308.1796v4, p. 8, Lemma 2, eq. (3.4): under A-1–A-5, B-2 (with
`α ∈ (0, 1/2]`) and B-3, for every `0 < p ≤ p₀`, both `sup_{0 ≤ t ≤ T} 𝔼|X(t)|^p` and
`sup_{n ≥ 1} sup_{0 ≤ t ≤ T} 𝔼|Xₙ(t)|^p` are finite.
The dependence clause `C := C(p, T, K, 𝔼[|X(0)|^p])` is not formalized. -/
theorem moment_bounds
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
    (hA1 : CondA1 T b) (hA2 : CondA2 T b) (hA3 : CondA3 T p₁ b σ) (hA4 : CondA4 T p₀ b σ)
    (hA5 : CondA5 P p₀ ξ)
    (α : ℝ) (hα : 0 < α ∧ α ≤ 1 / 2)
    (hB2 : CondB2 T α b σ bₙ σₙ)
    (hB3 : CondB3 T p₀ bₙ σₙ)
    (X : ℝ≥0 → Ω → SDEState d) (hX : IsSolution P ℱ W T ξ b σ X)
    (Xₙ : ℕ → ℝ≥0 → Ω → SDEState d)
    (hXₙ : ∀ n : ℕ, 1 ≤ n → IsSchemeSolution P ℱ W T ξ bₙ σₙ n (Xₙ n)) :
    ∀ p : ℝ, 0 < p → p ≤ p₀ →
      (⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ∫⁻ ω, ‖X t ω‖ₑ ^ p ∂P) < ⊤ ∧
      (⨆ n ∈ {n : ℕ | 1 ≤ n}, ⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ∫⁻ ω, ‖Xₙ n t ω‖ₑ ^ p ∂P) < ⊤ := by sorry

end SabanisEuler.Rate
