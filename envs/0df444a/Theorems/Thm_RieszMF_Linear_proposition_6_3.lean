-- Prove2me | Theorems.Thm_RieszMF_Linear_proposition_6_3
-- name    : RieszMF.Linear.proposition_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:57.603976+00:00
-- url     : https://prove2.me/theorems/0938387b-0783-4074-8b25-4716fb6022b7
-- title:
--   Proposition 6.3, p. 32 — the expected modulated energy grows by at most $2\sigma$ times the diffusion term plus the commutator term (6.16)
-- statement:
--   Let $d\ge3$, $0\le s<d-2$, $\sigma>0$, let $\mathbb M$ satisfy $\mathbb M\xi\cdot\xi\le0$ and let $\mathsf g$ be an admissible potential with radius $r_0$.
--   Let $\mu^0\in\mathcal P(\mathbb R^d)\cap L^\infty$ (with finite log moment if $s=0$) and let $\mu\in C([0,\infty);\mathcal P(\mathbb R^d)\cap L^\infty(\mathbb R^d))$ be the mild solution of (1.5) from $\mu^0$; put $u^\kappa=\mathbb M\nabla\mathsf g*\mu^\kappa$. Let $N\ge1$, $x^0_N$ pairwise distinct, $W_1,\dots,W_N$ independent standard Brownian motions in $\mathbb R^d$ on a probability space, and $x_N$ the solution of (1.1) from $x^0_N$, with $\mu^\kappa_N=\frac1N\sum_i\delta_{x^\kappa_i}$. Then for all $t\ge0$
--   $$\mathbb E\big(F_N(x^t_N,\mu^t)-F_N(x^0_N,\mu^0)\big)\le2\sigma\,\mathbb E\Big(\int_0^t\!\!\int_{(\mathbb R^d)^2\setminus\triangle}\Delta\mathsf g(x-y)\,d(\mu^\kappa_N-\mu^\kappa)^{\otimes2}d\kappa\Big)+\mathbb E\Big(\int_0^t\Big|\int_{(\mathbb R^d)^2\setminus\triangle}(u^\kappa(x)-u^\kappa(y))\cdot\nabla\mathsf g(x-y)\,d(\mu^\kappa_N-\mu^\kappa)^{\otimes2}\Big|d\kappa\Big).$$
--
--   This is the rigorous form of the formal Itô inequality (1.7) and the starting point of both Gronwall arguments.
--
--   **Formalization Note.** The expectations may be infinite: $F_N(x^t_N,\mu^t)$ is bounded below but not above, the diffusion integral is bounded above but not below. Writing $A=F_N(x^t_N,\mu^t)-F_N(x^0_N,\mu^0)$, $D$ for the diffusion time integral and $Q\ge0$ for the commutator time integral, the inequality is stated in $[0,\infty]$ as $\mathbb E A^++2\sigma\,\mathbb E D^-\le\mathbb E A^-+2\sigma\,\mathbb E D^++\mathbb E Q$, which is $\mathbb E A\le2\sigma\mathbb E D+\mathbb E Q$ whenever the latter is defined and avoids $\infty-\infty$. Expectations are lower Lebesgue integrals, so no default value of a divergent integral enters; the pathwise time integral of the diffusion term is an ordinary integral of a function that is continuous in $\kappa$ along collision-free paths.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 32, Proposition 6.3, (6.16)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem proposition_6_3 (d : ℕ) (hd : 3 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d - 2)
    (σ : ℝ) (hσ : 0 < σ) (M : Matrix (Fin d) (Fin d) ℝ) (hM : NegSemidef M)
    (g : E d → ℝ) (r₀ : ℝ) (hg : Admissible d s M g r₀)
    (μ0 : E d → ℝ) (μ : ℝ≥0 → E d → ℝ) (hμ0 : IsProbDensityLinfty μ0)
    (hlog : s = 0 → LogMoment μ0) (hμ : IsMildSolution d σ M g μ0 μ) (hμP : IsProbPath μ)
    (N : ℕ) (hN : 0 < N) (x0 : Fin N → E d) (hx0 : Pairwise (fun i j => x0 i ≠ x0 j))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin N → ℝ≥0 → Ω → E d) (x : Fin N → ℝ≥0 → Ω → E d)
    (hW : IsBrownianFamily P W) (hx : IsParticleSolution P σ M g x0 W x) (t : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal
        (modEnergy N g (fun i => x i t ω) (μ t) - modEnergy N g x0 μ0) ∂P)
      + ENNReal.ofReal (2 * σ) * ∫⁻ ω, ENNReal.ofReal
        (-∫ κ in (0 : ℝ)..(t : ℝ),
          offDiag N (fun a b => Δ g (a - b)) (fun i => x i κ.toNNReal ω) (μ κ.toNNReal)) ∂P
    ≤ (∫⁻ ω, ENNReal.ofReal
        (-(modEnergy N g (fun i => x i t ω) (μ t) - modEnergy N g x0 μ0)) ∂P)
      + ENNReal.ofReal (2 * σ) * ∫⁻ ω, ENNReal.ofReal
        (∫ κ in (0 : ℝ)..(t : ℝ),
          offDiag N (fun a b => Δ g (a - b)) (fun i => x i κ.toNNReal ω) (μ κ.toNNReal)) ∂P
      + ∫⁻ ω, (∫⁻ κ in Ioc (0 : ℝ) t, ENNReal.ofReal
        |offDiag N (fun a b => inner ℝ (velocity M g (μ κ.toNNReal) a - velocity M g (μ κ.toNNReal) b)
            (gradient g (a - b))) (fun i => x i κ.toNNReal ω) (μ κ.toNNReal)|) ∂P := by sorry

end RieszMF.Linear
