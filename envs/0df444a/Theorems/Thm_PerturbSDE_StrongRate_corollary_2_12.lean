-- Prove2me | Theorems.Thm_PerturbSDE_StrongRate_corollary_2_12
-- name    : PerturbSDE.StrongRate.corollary_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:29.55949+00:00
-- url     : https://prove2.me/theorems/3438d624-9c9b-4372-83ae-024760bf3cb5
-- title:
--   Corollary 2.12 (= Theorem 1.2), p. 15 — perturbation estimate with L^p local errors (finite-dimensional case H = ℝ^d, U = ℝ^m)
-- statement:
--   In the setting of Theorem 2.10 without the process $\chi$ (normal filtration, standard $m$-dimensional Brownian motion $W$, Borel $\mathcal O\subseteq\mathbb R^d$, measurable $\mu,\sigma$, $\varepsilon\in[0,\infty]$, $p\in[2,\infty)$, a stopping time $\tau:\Omega\to[0,T]$, $\mathcal O$-valued adapted continuous $X,Y$ solving $dX=\mu(X)dt+\sigma(X)dW$ and $dY=a\,dt+b\,dW$ with predictable $a,b$ and the same pathwise integrability), assume
--   $$\int_0^\tau\big[R_{p,\varepsilon}(X_s,Y_s)\big]^+ds<\infty\quad\mathbb P\text{-a.s.},\tag{56}$$
--   where $R_{p,\varepsilon}(x,y)=\big(\langle x-y,\mu(x)-\mu(y)\rangle+\frac{(p-1)(1+\varepsilon)}2\|\sigma(x)-\sigma(y)\|_{HS}^2\big)/\|x-y\|^2$. Then for all $\delta,\rho,r\in(0,\infty)$ and $q\in(0,\infty]$ with $\frac1p+\frac1q=\frac1r$,
--   $$\begin{aligned}\|X_\tau-Y_\tau\|_{L^r(\Omega)}\le{}&\Big\|\exp\Big(\int_0^\tau\Big[R_{p,\varepsilon}(X_s,Y_s)+\frac{1-\frac1p}{\delta}+\frac{\frac12-\frac1p}{\rho}\Big]^+ds\Big)\Big\|_{L^q(\Omega)}\\&\cdot\Big[\|X_0-Y_0\|_{L^p(\Omega)}+\delta^{1-\frac1p}\|a-\mu(Y)\|_{L^p([\![0,\tau]\!])}+\rho^{\frac12-\frac1p}\sqrt{(p-1)(1+1/\varepsilon)}\,\|b-\sigma(Y)\|_{L^p([\![0,\tau]\!];HS)}\Big].\end{aligned}$$
--
--   This is the form of the perturbation estimate used for numerical schemes: the right-hand side splits into an exponential moment and the $L^p$ norms of the local drift and diffusion errors. It is Theorem 1.2 of the introduction (with $(\alpha,\beta)$ for $(\delta,\rho)$).
--
--   **Formalization Note** Finite-dimensional case $H=\mathbb R^d$, $U=\mathbb R^m$, Hilbert–Schmidt norm on $\sigma$. Theorem 1.2 lets $r\in(0,\infty]$, but $\frac1p+\frac1q=\frac1r$ with $p<\infty$ forces $r<\infty$, so the two statements coincide. Everything on the right is computed in $[0,\infty]$ with $0\cdot\infty=0$ and $1/0=\infty$; at $\varepsilon=0$ the square root is $\infty$. Conventions for $X$, $Y$, $W$, the filtration and predictability as in Theorem 2.10; $L^p([\![0,\tau]\!])$ is with respect to $\lambda\otimes\mathbb P$ restricted to the stochastic interval.
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, p. 15, Corollary 2.12, (56); = Theorem 1.2, pp. 3–4, (5)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_PerturbSDE_StrongRate_Setting
import Definitions.Def_PerturbSDE_StrongRate_Perturbation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz SabanisEuler.Shared

/-- Hutzenthaler–Jentzen, arXiv:1401.0295v1, p. 15, Corollary 2.12 (= Theorem 1.2, pp. 3–4),
finite-dimensional case `H = ℝ^d`, `U = ℝ^m`: under (56), for all `δ, ρ, r ∈ (0, ∞)` and
`q ∈ (0, ∞]` with `1/p + 1/q = 1/r`,
`‖X_τ − Y_τ‖_{L^r} ≤ ‖exp(∫_0^τ [ratio + (1 − 1/p)/δ + (1/2 − 1/p)/ρ]^+ ds)‖_{L^q}
  · [ ‖X_0 − Y_0‖_{L^p} + δ^{1−1/p} ‖a − µ(Y)‖_{L^p(⟦0,τ⟧)}
      + ρ^{1/2−1/p} √((p−1)(1+1/ε)) ‖b − σ(Y)‖_{L^p(⟦0,τ⟧)} ]`, in `[0, ∞]`, for `ε ∈ [0, ∞]`. -/
theorem corollary_2_12 {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {Ω : Type*}
    [mΩ : MeasurableSpace Ω]
    (T : ℝ≥0) (hT : 0 < T) (𝒪 : Set (SDEState d)) (h𝒪 : MeasurableSet 𝒪)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsWienerMartingale P ℱ W)
    (mu : SDEState d → SDEState d) (sigma : SDEState d → Diffusion d m)
    (hmu : Measurable mu) (hsigma : Measurable sigma)
    (ε : ℝ≥0∞) (p : ℝ) (hp : 2 ≤ p) (τ : Ω → ℝ≥0) (hτ : IsStopTime P ℱ T τ)
    (X Y : ℝ≥0 → Ω → SDEState d) (hX𝒪 : ∀ t ≤ T, ∀ ω, X t ω ∈ 𝒪)
    (hY𝒪 : ∀ t ≤ T, ∀ ω, Y t ω ∈ 𝒪)
    (a : ℝ≥0 → Ω → SDEState d) (b : ℝ≥0 → Ω → Diffusion d m)
    (ha : IsStronglyPredictable ℱ a) (hb : IsStronglyPredictable ℱ b)
    (hint : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖a s.toNNReal ω‖ₑ + ‖b s.toNNReal ω‖ₑ ^ 2 + ‖mu (X s.toNNReal ω)‖ₑ +
        ‖sigma (X s.toNNReal ω)‖ₑ ^ 2 + ‖mu (Y s.toNNReal ω)‖ₑ +
        ‖sigma (Y s.toNNReal ω)‖ₑ ^ 2) < ⊤)
    (hX : IsSolution P ℱ W T (X 0) (fun z => mu z.2) (fun z => sigma z.2) X)
    (hY : IsItoProcess P ℱ W T (Y 0) a b Y)
    (h56 : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) (τ ω),
      (monoRatio mu sigma p ε (X s.toNNReal ω) (Y s.toNNReal ω)).toENNReal < ⊤) :
    ∀ δ ρ r : ℝ, 0 < δ → 0 < ρ → 0 < r → ∀ q : ℝ≥0∞, q ≠ 0 →
      (ENNReal.ofReal p)⁻¹ + q⁻¹ = (ENNReal.ofReal r)⁻¹ →
      eLpNorm (fun ω => X (τ ω) ω - Y (τ ω) ω) (ENNReal.ofReal r) P ≤
        eLpNorm (expPosIntegral
            (fun s ω => monoRatio mu sigma p ε (X s ω) (Y s ω) +
              (((1 - 1 / p) / δ + (1 / 2 - 1 / p) / ρ : ℝ) : EReal)) τ) q P *
          (eLpNorm (fun ω => X 0 ω - Y 0 ω) (ENNReal.ofReal p) P +
            ENNReal.ofReal (δ ^ (1 - 1 / p)) *
              eLpNorm (fun z : ℝ × Ω => a z.1.toNNReal z.2 - mu (Y z.1.toNNReal z.2))
                (ENNReal.ofReal p) (onStochInterval P τ) +
            ENNReal.ofReal (ρ ^ (1 / 2 - 1 / p)) *
              (ENNReal.ofReal (p - 1) * (1 + ε⁻¹)) ^ (1 / 2 : ℝ) *
              eLpNorm (fun z : ℝ × Ω => b z.1.toNNReal z.2 - sigma (Y z.1.toNNReal z.2))
                (ENNReal.ofReal p) (onStochInterval P τ)) := by sorry

end PerturbSDE.StrongRate
