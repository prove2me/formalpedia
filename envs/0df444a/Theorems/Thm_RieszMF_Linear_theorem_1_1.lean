-- Prove2me | Theorems.Thm_RieszMF_Linear_theorem_1_1
-- name    : RieszMF.Linear.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:11.711451+00:00
-- url     : https://prove2.me/theorems/2593aa65-4109-4243-9d27-48ac25861574
-- title:
--   Theorem 1.1, p. 6 — $\mathbb E|F_N(x^t_N,\mu^t)|\le C(1+t+t^{\frac{\sigma+C}\sigma}\mathbf 1_{s=0})(|F_N(x^0_N,\mu^0)|+N^{-\beta})$ for admissible sub-Coulombic potentials
-- statement:
--   Let $d\ge3$ and $0\le s<d-2$. There is an exponent $\beta>0$, depending only on $s$ and $d$, with the following property. Let $\sigma>0$, let $\mathbb M$ be a $d\times d$ matrix with $\mathbb M\xi\cdot\xi\le0$ for all $\xi$, and let $\mathsf g$ be an admissible potential (assumptions (i)–(x), radius $r_0$). For every value $L$ of $\|\mu^0\|_{L^\infty}$ there are a constant $C>0$ and a threshold $N_0$ such that: whenever
--
--   1. $\mu^0\in\mathcal P(\mathbb R^d)\cap L^\infty(\mathbb R^d)$ with $\|\mu^0\|_{L^\infty}=L$, and $\int\log(1+|x|)\,d\mu^0<\infty$ if $s=0$;
--   2. $\mu\in C([0,\infty);\mathcal P(\mathbb R^d)\cap L^\infty(\mathbb R^d))$ is a (mild) solution of $\partial_t\mu=-\operatorname{div}(\mu\,\mathbb M\nabla\mathsf g*\mu)+\sigma\Delta\mu$ with $\mu|_{t=0}=\mu^0$;
--   3. $N\ge N_0$, $x^0_N\in(\mathbb R^d)^N$ has distinct points, and $x_N$ solves the particle system $dx^t_i=\frac1N\sum_{j\ne i}\mathbb M\nabla\mathsf g(x^t_i-x^t_j)dt+\sqrt{2\sigma}\,dW^t_i$, $x^t_i|_{t=0}=x^0_i$, driven by independent standard Brownian motions on some probability space,
--
--   we have for all $t\ge0$
--   $$\mathbb E\big(|F_N(x^t_N,\mu^t)|\big)\le C\Big(1+t+t^{\frac{\sigma+C}{\sigma}}\mathbf 1_{s=0}\Big)\Big(|F_N(x^0_N,\mu^0)|+N^{-\beta}\Big).$$
--
--   The modulated energy $F_N$ measures the distance between the empirical measure of the particles and the solution of the mean-field equation; the theorem gives a quantitative mean-field limit whose error grows at most linearly in time when $s>0$.
--
--   **Formalization Note.** The quantifier order encodes the dependencies: $\beta$ depends on $s,d$ only; $C$ and $N_0$ are chosen after $\sigma$, $\mathbb M$, $\mathsf g$ (with $r_0$) and $L=\|\mu^0\|_{L^\infty}$, before the data, the configuration, the probability space, the noise and $t$ (the paper lists $s,d,\sigma,\|\mu\|_{L^\infty},\mathsf g$ for $C$ and $\|\mu^0\|_{L^\infty}$ for $N_0$; $\mathbb M$ enters through $u=\mathbb M\nabla\mathsf g*\mu$). The same $C$ is the prefactor and appears in the exponent $(\sigma+C)/\sigma$, as printed. The expectation is a lower Lebesgue integral of $|F_N|$, so it cannot take a default value. "$\|\mu\|_{L^\infty}$" in the dependency list is $\|\mu^0\|_{L^\infty}$ (Remark 3.4).
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 6, Theorem 1.1, (1.18)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem theorem_1_1 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → 0 ≤ s → s < (d : ℝ) - 2 →
    ∃ β : ℝ, 0 < β ∧
    ∀ (σ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : E d → ℝ) (r₀ : ℝ),
      0 < σ → NegSemidef M → Admissible d s M g r₀ →
    ∀ L : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ (μ0 : E d → ℝ) (μ : ℝ≥0 → E d → ℝ),
      lpNorm μ0 ⊤ = L → IsProbDensityLinfty μ0 → (s = 0 → LogMoment μ0) →
      IsMildSolution d σ M g μ0 μ → IsProbPath μ →
    ∀ N : ℕ, N₀ ≤ N → 0 < N →
    ∀ x0 : Fin N → E d, Pairwise (fun i j => x0 i ≠ x0 j) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : Fin N → ℝ≥0 → Ω → E d) (x : Fin N → ℝ≥0 → Ω → E d),
      IsBrownianFamily P W → IsParticleSolution P σ M g x0 W x →
    ∀ t : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal |modEnergy N g (fun i => x i t ω) (μ t)| ∂P
        ≤ ENNReal.ofReal (C * (1 + t + (t : ℝ) ^ ((σ + C) / σ) * (if s = 0 then 1 else 0))
            * (|modEnergy N g x0 μ0| + (N : ℝ) ^ (-β))) := by sorry

end RieszMF.Linear
