-- Prove2me | Theorems.Thm_PropagatorLimit_Scaling_theorem_3_3
-- name    : PropagatorLimit.Scaling.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:10.995978+00:00
-- url     : https://prove2.me/theorems/119d13d1-3917-49e4-8cdd-d62f5ab88acc
-- title:
--   Theorem 3.3, p. 7 — the nonlinear propagator model converges stably in law to the linear impact model with stochastic liquidity λ_t
-- statement:
--   Let $(\Omega,\mathcal F,(\mathcal F_t),P)$ carry a Brownian pair $(W,W^\perp)$ and the order flow of p. 5, an Itô process $F\in\mathcal L^2$ with
--   $$dF_t=\mu_t\,dt+v_t\,dW_t,\qquad dv_t=a_t\,dt+\eta_t\,dW_t+b_t\,dW^\perp_t,$$
--   where $\mu,a,\eta,b$ are locally bounded càdlàg processes and $v>0$. Let $T>0$, $\beta>0$, and let $g$ be odd, $C^1$, concave on $[0,\infty)$, with $|g(x)|+|g'(x)|\le C(1+|x|)$. For $N\ge1$ let $I^N$ be the nonlinear propagator model (2.1) with the scaling (3.1),
--   $$\Delta I^N_n=-\beta I^N_{n-1}\Delta t^N+\sqrt{\Delta t^N}\,g\Big(\tfrac1{\sqrt{\Delta t^N}}\Delta F^N_n\Big),\qquad I^N_0=0,\quad \Delta t^N=T/N,$$
--   viewed as the step path $t\mapsto I^N_{\lceil t/\Delta t^N\rceil}$ on $[0,T]$. With $\phi_v$ the centred Gaussian density with standard deviation $v$, set
--   $$\lambda_t=\int g'(x)\phi_{v_t}(x)\,dx,\quad \chi_t=\frac12\int(v_t^{-2}x^2-1)g'(x)\phi_{v_t}(x)\,dx,\quad \theta_t=\sqrt{\lambda_t^2v_t^2+\zeta_t^2-2\lambda_th_t},$$
--   $$\zeta_t=\sqrt{\int g^2(x)\phi_{v_t}(x)\,dx},\qquad h_t=\int xg(x)\phi_{v_t}(x)\,dx.$$
--
--   Then, as $N\to\infty$, $I^N$ converges stably in law to the **linear** impact model
--   $$dI_t=-\beta I_t\,dt+\lambda_t\,dF_t+\eta_t\chi_t\,dt+\theta_t\,dW'_t,\qquad I_0=0,$$
--   where $W'$ is a Brownian motion on a very good extension of the filtered probability space whose quadratic covariation with $W$ is
--   $$d[W,W']_t=\frac1{\theta_t}\Big(\frac{h_t}{v_t}-\lambda_tv_t\Big)dt.$$
--
--   The theorem says that a nonlinear (concave) microstructure impact becomes, in the diffusive scaling limit, linear impact with a stochastic illiquidity parameter $\lambda_t$ driven by the volatility of order flow; the limit model is the one used for the optimal trading results of §4.
--
--   **Formalization Note** "Converges (stably in law) to the linear impact model" is read existentially: there are a very good extension, a Brownian motion $W'$ on it with the printed covariation, and a continuous solution $I$ of (3.2) such that the step paths of $I^N$ converge stably in law to $I$ on $[0,T]$. A universal reading (for every such $W'$ and $I$) would be false, because the covariation with $W$ does not determine the joint law of $W'$ with $W^\perp$ and other martingales. Stable convergence is tested against bounded measurable variables times bounded path functionals that are Lipschitz for the uniform distance on $[0,T]$. Three hypotheses are **added** and disclosed: the growth bound on $g$ (needed by Assumption A.2(c), p. 25, in the paper's own proof), $I^N_0=0$ (as in the explicit solution, p. 27) and $I_0=0$ (§4.1, p. 10). The step path uses $\lceil t/\Delta t^N\rceil$, Theorem A.3's $\lceil Nt\rceil$ for a general horizon. The coefficients $\theta_t$ and the covariation density are kept as printed.
-- source:
--   Muhle-Karbe, Wang & Webster, Stochastic liquidity as a proxy for nonlinear price impact, SSRN 4286108 (version of November 2, 2023), p. 7, Theorem 3.3 (with Definition 2.1, p. 4, (3.1), p. 6, and the order flow of p. 5)

import Mathlib
import Definitions.Def_PropagatorLimit_Scaling_Model

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace PropagatorLimit.Scaling

/-- Theorem 3.3, p. 7: the step paths of the nonlinear propagator model (2.1) with the scaling
(3.1) converge stably in law on `[0, T]` to a solution `I` of the linear impact model (3.2),
driven by a Brownian motion `W′` on a very good extension with
`d[W, W′]_t = (1/θ_t)(h_t/v_t − λ_t v_t) dt`. -/
theorem theorem_3_3 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W Wperp : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianPair P 𝓕 W Wperp)
    (T : ℝ≥0) (hT : 0 < T) (fl : Flow Ω) (hfl : IsFlow P 𝓕 W Wperp T fl)
    (beta : ℝ) (hbeta : 0 < beta) (g : ℝ → ℝ) (hg : IsImpactFn g) :
    ∃ (E : Extension Ω P 𝓕) (Wp : ℝ≥0 → E.Ω' → ℝ) (I : ℝ≥0 → E.Ω' → ℝ),
      E.IsVeryGood ∧ IsFBrownian E.P' E.𝓖 Wp ∧
      EthierKurtz.HasCrossVariation E.P' (fun t ω' => W t (E.π ω')) Wp
        (fun t ω' => ∫ u in (0 : ℝ)..t.val, rho g (fl.v u.toNNReal (E.π ω'))) ∧
      SolvesLinearImpact beta g W fl E Wp I ∧
      StablyConverges P T (fun N ω => INpath beta T g fl.F N ω) E (fun ω' t => I t ω') := by sorry

end PropagatorLimit.Scaling
