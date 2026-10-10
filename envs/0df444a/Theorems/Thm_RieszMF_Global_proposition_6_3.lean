-- Prove2me | Theorems.Thm_RieszMF_Global_proposition_6_3
-- name    : RieszMF.Global.proposition_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:58.498264+00:00
-- url     : https://prove2.me/theorems/93602a16-0e39-471b-9490-54cd74cf8aa9
-- title:
--   Proposition 6.3, p. 32 — $\mathbb E(F_N(x^t_N,\mu^t)-F_N(x^0_N,\mu^0))\le2\sigma\mathbb E\int_0^t\iint\Delta\mathsf g+\mathbb E\int_0^t|\text{commutator}|$
-- statement:
--   Let $d\ge3$, $0\le s<d-2$, $\sigma>0$, $\mathbb M$ with (1.2) and $\mathsf g$ admissible. Let $x_N$ be the solution of (1.1) from pairwise distinct $x^0_N$, driven by independent standard Brownian motions, and let $\mu\in C([0,\infty);\mathcal P(\mathbb R^d)\cap L^\infty)$ solve (1.5) (with $\int\log(1+|x|)\,d\mu^0<\infty$ if $s=0$); put $u^\kappa=\mathbb M\nabla\mathsf g*\mu^\kappa$ and $\mu^\kappa_N=\frac1N\sum_i\delta_{x^\kappa_i}$. Then for all $t\ge0$,
--
--   $$\mathbb E\big(F_N(x^t_N,\mu^t)-F_N(x^0_N,\mu^0)\big)\le2\sigma\,\mathbb E\Big(\int_0^t\int_{(\mathbb R^d)^2\setminus\triangle}\Delta\mathsf g(x-y)\,d(\mu^\kappa_N-\mu^\kappa)^{\otimes2}\,d\kappa\Big)+\mathbb E\Big(\int_0^t\Big|\int_{(\mathbb R^d)^2\setminus\triangle}(u^\kappa(x)-u^\kappa(y))\cdot\nabla\mathsf g(x-y)\,d(\mu^\kappa_N-\mu^\kappa)^{\otimes2}\Big|\,d\kappa\Big).$$
--
--   This is the rigorous form of the modulated-energy evolution inequality: the stochastic integrals of Itô's formula have vanished in expectation, the diffusion contributes the term with $\Delta\mathsf g$, and the transport contributes a commutator.
--
--   **Formalization Note** Expectations are taken without assuming integrability. With $A=F_N(x^t_N,\mu^t)-F_N(x^0_N,\mu^0)$, $D(\kappa)$ the $\Delta\mathsf g$-term and $K(\kappa)$ the commutator term, the inequality is stated as $\mathbb E A^++2\sigma\,\mathbb E\!\int_0^tD^-\le\mathbb E A^-+2\sigma\,\mathbb E\!\int_0^tD^++\mathbb E\!\int_0^tK$ in $[0,\infty]$, which is the displayed inequality whenever its terms are defined and never compares $+\infty-\infty$ with anything. The expectation of $\int_0^tD$ is read as the integral over $\Omega\times[0,t]$.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 32, Proposition 6.3, (6.16); standing setting p. 6

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Proposition 6.3 (p. 32), (6.16), in the standing setting of Theorem 1.1. Write
`A = F_N(x^t_N, μ^t) - F_N(x^0_N, μ^0)`, `D(κ) = ∫∫_{△ᶜ} Δg(x - y) d(μ^κ_N - μ^κ)^{⊗2}` and
`K(κ) = |∫∫_{△ᶜ} (u^κ(x) - u^κ(y))·∇g(x - y) d(μ^κ_N - μ^κ)^{⊗2}|`, `u^κ = 𝕄∇g ∗ μ^κ`.
The inequality `𝔼A ≤ 2σ 𝔼∫_0^t D + 𝔼∫_0^t K` is stated with positive and negative parts
moved across, `𝔼A⁺ + 2σ 𝔼∫_0^t D⁻ ≤ 𝔼A⁻ + 2σ 𝔼∫_0^t D⁺ + 𝔼∫_0^t K`, in `[0, ∞]`. -/
theorem proposition_6_3 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → 0 ≤ s → s < (d : ℝ) - 2 →
    ∀ (σ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ) (r₀ : ℝ),
      0 < σ → RieszMF.Linear.NegSemidef M → Admissible d s M g r₀ →
    ∀ (μ0 : RieszMF.Linear.E d → ℝ) (μ : ℝ≥0 → RieszMF.Linear.E d → ℝ),
      IsMildSolution d σ M g μ0 μ → RieszMF.Linear.IsProbPath μ → (s = 0 → RieszMF.Linear.LogMoment μ0) →
    ∀ N : ℕ, 0 < N →
    ∀ x0 : Fin N → RieszMF.Linear.E d, Pairwise (fun i j => x0 i ≠ x0 j) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : Fin N → ℝ≥0 → Ω → RieszMF.Linear.E d) (x : Fin N → ℝ≥0 → Ω → RieszMF.Linear.E d),
      IsBrownianFamily P W → IsParticleSolution P σ M g x0 W x →
    ∀ t : ℝ≥0,
      let A : Ω → ℝ := fun ϖ =>
        RieszMF.Linear.modEnergy N g (fun i => x i t ϖ) (μ t) - RieszMF.Linear.modEnergy N g x0 μ0
      let D : ℝ → Ω → ℝ := fun κ ϖ =>
        RieszMF.Linear.offDiag N (fun a b => lap g (a - b)) (fun i => x i κ.toNNReal ϖ) (μ κ.toNNReal)
      let K : ℝ → Ω → ℝ := fun κ ϖ =>
        |RieszMF.Linear.offDiag N (fun a b => inner ℝ (velocity M g (μ κ.toNNReal) a -
            velocity M g (μ κ.toNNReal) b) (gradient g (a - b)))
          (fun i => x i κ.toNNReal ϖ) (μ κ.toNNReal)|
      (∫⁻ ϖ, ENNReal.ofReal (A ϖ) ∂P) +
          ENNReal.ofReal (2 * σ) *
            ∫⁻ ϖ, ∫⁻ κ in Icc (0 : ℝ) t, ENNReal.ofReal (-D κ ϖ) ∂volume ∂P ≤
        (∫⁻ ϖ, ENNReal.ofReal (-A ϖ) ∂P) +
          ENNReal.ofReal (2 * σ) *
            ∫⁻ ϖ, ∫⁻ κ in Icc (0 : ℝ) t, ENNReal.ofReal (D κ ϖ) ∂volume ∂P +
          ∫⁻ ϖ, ∫⁻ κ in Icc (0 : ℝ) t, ENNReal.ofReal (K κ ϖ) ∂volume ∂P := by sorry

end RieszMF.Global
