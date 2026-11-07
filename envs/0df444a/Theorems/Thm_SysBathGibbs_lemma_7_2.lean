-- Prove2me | Theorems.Thm_SysBathGibbs_lemma_7_2
-- name    : SysBathGibbs.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:43.064791+00:00
-- url     : https://prove2.me/theorems/454fba89-4c33-4318-979d-673b29164ebf
-- title:
--   Lemma 7.2 — An integrable correction kernel $\nu_{T_0}$
-- statement:
--   Let $h$, $\nu_0$ and $\nu_{T_0}$ be as in (7.7). The function $\nu_0$ is purely imaginary and exponentially decaying: there are $C_1,a>0$ with $|\nu_0(t)|\le C_1e^{-a|t|}$ and $\operatorname{Re}\nu_0(t)=0$ for all $t$. Moreover there is $C>0$ such that for every $T_0>0$: $\nu_{T_0}$ and $t\mapsto|t||\nu_{T_0}(t)|$ are integrable,
--   $$
--   \hat\nu_{T_0}(\omega)=\frac{\omega\hat\mu_{T_0}(\omega)}{1-\hat\mu_{T_0}(2\omega)}\ (\omega\ne0),\qquad \hat\nu_{T_0}(0)=\frac i{10T_0},\qquad \|\nu_{T_0}\|_1\le\frac C{T_0},\qquad \int_{\mathbb R}|t||\nu_{T_0}(t)|\,dt\le C,
--   $$
--   where $\hat\nu(\omega)=\int\nu(t)e^{i\omega t}dt$ as in (2.10).
--
--   The kernel defines the correction $X$ of the approximate stationary state, and these bounds give its size.
--
--   Differences from the source:
--   - encoding: "exponentially decaying" → ∃ C1 a > 0, |ν0(t)| ≤ C1 e^{−a|t|}; reason: the standard meaning, as proved on p.58
--   - encoding: the quotient at ω = 0 understood as its continuous extension i/(10T0) → the value of ν̂_{T0}(0) stated separately; reason: the quotient is 0/0 there
--   - encoding: ‖ν_{T0}‖₁ and ∫|t||ν_{T0}| as numbers → integrability stated as conclusions alongside the bounds; reason: rules out a junk integral value
--   - encoding: "T0 is a parameter" of (1.6) → T0 > 0; reason: the law (7.1) is defined for T0 > 0
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Lemma 7.2 (eq. (7.13)), p.58

import Definitions.Def_SysBathGibbs_Stationary

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Lemma 7.2 (An integrable correction kernel)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.58.
`ν₀` of (7.7) is purely imaginary and exponentially decaying. For every `T₀ > 0`,
`ν̂_{T₀}(ω) = ω μ̂_{T₀}(ω)/(1 - μ̂_{T₀}(2ω))`, `‖ν_{T₀}‖₁ ≤ C/T₀`, `∫ |t||ν_{T₀}(t)| dt ≤ C`. At `ω = 0` the
quotient is understood as its continuous extension, with value `i/(10T₀)`.

**Formalization Note.** "Exponentially decaying" is `|ν₀(t)| ≤ C₁ e^{-a|t|}` for some `C₁, a > 0`. The
Fourier transform follows (2.10), `ν̂(ω) = ∫ ν(t) e^{iωt} dt`. The integrability of `ν_{T₀}` is
stated so that the `L¹` norm is not a junk value. -/
theorem lemma_7_2 :
    (∃ C₁ a : ℝ, 0 < C₁ ∧ 0 < a ∧
      ∀ t : ℝ, (nu0 t).re = 0 ∧ ‖nu0 t‖ ≤ C₁ * Real.exp (-a * |t|)) ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ T₀ : ℝ, 0 < T₀ →
        Integrable (nuT T₀) ∧
        Integrable (fun t => |t| * ‖nuT T₀ t‖) ∧
        (∀ w : ℝ, w ≠ 0 →
          ∫ t : ℝ, nuT T₀ t * Complex.exp (Complex.I * w * t) =
            (w : ℂ) * muHat T₀ w / (1 - muHat T₀ (2 * w))) ∧
        (∫ t : ℝ, nuT T₀ t = Complex.I / (10 * T₀)) ∧
        (∫ t : ℝ, ‖nuT T₀ t‖) ≤ C / T₀ ∧
        (∫ t : ℝ, |t| * ‖nuT T₀ t‖) ≤ C := by sorry

end SysBathGibbs
