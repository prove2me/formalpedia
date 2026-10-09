-- Prove2me | Theorems.Thm_QuantumZipper_Welding_theorem_4_5
-- name    : QuantumZipper.Welding.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:39.115862+00:00
-- url     : https://prove2.me/theorems/15e9b86e-fc09-47df-91b5-70b09d14d791
-- title:
--   Theorem 4.5 — reverse $\mathrm{SLE}_{\kappa,\rho}$ zipping preserves the law of $\hat{\mathfrak h}_0+\tilde h$
-- statement:
--   Fix $\kappa>0$ and a signed measure $\rho=\rho_+-\rho_-$ with finite positive and negative mass, supported on a closed set $\mathcal C\subseteq\overline{\mathbb H}$. Let $f_t=g_t-W_t$ be the reverse Loewner flow
--   $$df_t(z)=\frac{-2}{f_t(z)}\,dt-dW_t,\qquad dW_t=\Big(\int\operatorname{Re}\frac{-1}{f_t(y)}\,\rho(dy)\Big)dt+\sqrt\kappa\,dB_t,$$
--   run up to a stopping time $T$ of the filtration of $B$, at or before the first time $0\in f_t(\mathcal C)$. Let
--   $$\hat{\mathfrak h}_t(z)=\mathfrak h_t(z)+\frac1{2\sqrt\kappa}\int G\big(f_t(y),f_t(z)\big)\rho(dy)$$
--   as in (4.4), and let $\tilde h$ be a free boundary GFF independent of $B$. Then the random distributions (modulo additive constants)
--   $$\hat{\mathfrak h}_0+\tilde h\qquad\text{and}\qquad\hat{\mathfrak h}_T+\tilde h\circ f_T$$
--   agree in law.
--
--   The theorem extends Theorem 1.2 (the case $\rho=0$) to the processes $\mathrm{SLE}_{\kappa,\rho}$ and is the input to Proposition 5.4 and Lemma 5.6.
--
--   **Formalization Note** Agreement in law is stated through the pairings with every mean-zero test function $\rho'$; by Proposition 3.1 these one-dimensional laws determine the law of a random modulo-constant distribution. Given $B$, $(\hat{\mathfrak h}_T+\tilde h\circ f_T,\rho')$ is Gaussian with mean $(\hat{\mathfrak h}_T,\rho')$ and variance $E_T(\rho')=\iint\rho'(y)G(f_Ty,f_Tz)\rho'(z)$. The conclusion is therefore
--   $$\mathbb E\Big[e^{is(\hat{\mathfrak h}_T,\rho')-\frac{s^2}2E_T(\rho')}\Big]=e^{is(\hat{\mathfrak h}_0,\rho')-\frac{s^2}2E_0(\rho')}\quad\text{for all }s\in\mathbb R.$$
--   The paper prints "closed $\mathcal C\subset\mathbb H$", but the stopping rule ("$f_t$ extended continuously to $\overline{\mathbb H}$") and Lemma 5.6 (a Dirac mass at a real point) need $\mathcal C\subseteq\overline{\mathbb H}$. The flow is pathwise and $T$ is finite-valued.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Theorem 4.5, pp. 51–52, (4.4)–(4.6)

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Welding

/-- **Theorem 4.5** (Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2,
Theorem 4.5, pp. 51–52). Fix `κ > 0` and a signed measure `ρ = ρ₊ − ρ₋` (finite positive and finite
negative mass) supported on a closed set `𝒞 ⊆ ℍ̄`. Let `f_t = g_t − W_t` be the reverse Loewner
flow (4.5) whose driving function solves (4.6),
`W_t = √κ B_t + ∫₀ᵗ ∫ Re(−1/f_s(y)) ρ(dy) ds`, run up to a stopping time `T` (of the filtration of
`B`) at or before the first time `0 ∈ f_t(𝒞)`. With
`ĥ_t(z) = 𝔥_t(z) + (1/(2√κ)) ∫ G_t(y, z) ρ(dy)` (4.4) and `h̃` a free boundary GFF independent of
`B`, the random distributions (modulo additive constants) `ĥ₀ + h̃` and `ĥ_T + h̃ ∘ f_T` agree in law.

**Formalization Note**
* "Agree in law" is stated through the one-dimensional laws of the pairings with mean-zero test
  functions `ρ'`, which determine the law of a random modulo-additive-constant distribution
  (Proposition 3.1, p. 42; finite families reduce to one test function `Σ t_j ρ'_j` by linearity).
  Given `B`, `(ĥ_T + h̃ ∘ f_T, ρ')` is Gaussian with mean `(ĥ_T, ρ')` and variance
  `E_T(ρ') = ∫∫ ρ'(y) G(f_T y, f_T z) ρ'(z)` (footnote 1, p. 7; `h̃` independent of `B`), so its law is
  the mixture over `B`; the conclusion equates the characteristic function of that mixture with the
  one of `N((ĥ₀, ρ'), E₀(ρ'))`, the law of `(ĥ₀ + h̃, ρ')`.
* The paper prints "supported on some closed `𝒞 ⊂ ℍ`", but the stopping rule "`0 ∈ f_t(𝒞)` (here
  `f_t` is extended continuously from `ℍ` to `ℍ̄`)" and the use in Lemma 5.6 (a Dirac mass at a real
  point) need `𝒞 ⊆ ℍ̄`; this reading is disclosed.
* The flow is pathwise: `g` solves the reverse Loewner ODE driven by `W` on `ℍ` and at the real
  points of `𝒞` (until they reach `0`), `W` is continuous, and (4.6) holds as an integral equation on
  `[0, T]`. The stopping time `T` is finite-valued (`ℝ≥0`).
* `ρ₊`, `ρ₋` are finite measures (no energy condition, as on p. 51). -/
theorem theorem_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ)
    (𝒞 : Set ℂ) (h𝒞 : IsClosed 𝒞) (h𝒞H : 𝒞 ⊆ {z : ℂ | 0 ≤ z.im})
    (ρp ρn : Measure ℂ) [IsFiniteMeasure ρp] [IsFiniteMeasure ρn]
    (hρp : ρp 𝒞ᶜ = 0) (hρn : ρn 𝒞ᶜ = 0)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (W : Ω → ℝ≥0 → ℝ) (g : Ω → ℝ≥0 → ℂ → ℂ) (T : Ω → ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[natSigma B t] {ω | T ω ≤ t})
    (hW_meas : ∀ t : ℝ≥0, Measurable fun ω => W ω t)
    (hg_meas : ∀ (t : ℝ≥0) (z : ℂ), Measurable fun ω => g ω t z)
    (hflow : ∀ᵐ ω ∂P,
      Continuous (W ω) ∧
      QuantumZipper.ReverseCoupling.IsReverseLoewnerFlow (W ω) (g ω) ∧
      (∀ x : ℝ, (x : ℂ) ∈ 𝒞 → IsRealPointFlow (W ω) (g ω) x) ∧
      (∀ t : ℝ≥0, t < T ω → ∀ y ∈ 𝒞, QuantumZipper.ReverseCoupling.revF (W ω) (g ω) t y ≠ 0) ∧
      IsSLEκρDriver κ (fun t => B t ω) (W ω) (g ω) ρp ρn (T ω)) :
    ∀ ρ : ℂ → ℝ, IsMeanZeroTest ρ → ∀ s : ℝ,
      ∫ ω, Complex.exp (Complex.I * ((s * pairing (hatH κ (W ω) (g ω) ρp ρn (T ω)) ρ : ℝ) : ℂ)
          - ((s ^ 2 / 2 * energyUnder (QuantumZipper.ReverseCoupling.revF (W ω) (g ω) (T ω)) ρ : ℝ) : ℂ)) ∂P =
        Complex.exp (Complex.I * ((s * pairing (hatH0 κ ρp ρn) ρ : ℝ) : ℂ)
          - ((s ^ 2 / 2 * energyUnder id ρ : ℝ) : ℂ)) := by sorry

end QuantumZipper.Welding
