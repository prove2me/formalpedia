-- Prove2me | Theorems.Thm_PropagatorLimit_Scaling_rescaled_convergence
-- name    : PropagatorLimit.Scaling.rescaled_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:03.336085+00:00
-- url     : https://prove2.me/theorems/e0d1f384-9dfb-4295-89a7-bed92739eb57
-- title:
--   Appendix A.1, p. 28 — √Δt Σ e^{βt_m} g(ΔF_m/√Δt) → e^{βt} I_t, I the linear impact model of Theorem 3.3
-- statement:
--   Let $(W,W^\perp)$ be a Brownian pair and $F$ the order flow of p. 5, $dF_t=\mu_t\,dt+v_t\,dW_t$ with positive Itô volatility $dv_t=a_t\,dt+\eta_t\,dW_t+b_t\,dW^\perp_t$. Let $T>0$, $\beta>0$, and let $g$ be an odd $C^1$ function, concave on $[0,\infty)$, with $|g(x)|+|g'(x)|\le C(1+|x|)$. Let $\Delta t^N=T/N$, $t^N_m=m\Delta t^N$, and let $\lambda_t,\chi_t,\theta_t$, $h_t$ be the coefficients of Theorem 3.3.
--
--   Then there is a very good extension carrying a Brownian motion $W'$ with $d[W,W']_t=\frac1{\theta_t}\big(\frac{h_t}{v_t}-\lambda_tv_t\big)dt$ and a solution $I$ of the linear impact model $dI_t=-\beta I_t\,dt+\lambda_t\,dF_t+\eta_t\chi_t\,dt+\theta_t\,dW'_t$, $I_0=0$, such that, with $n=\lceil t/\Delta t^N\rceil\wedge N$,
--   $$\sqrt{\Delta t^N}\sum_{m=1}^{n}e^{\beta t^N_m}g\Big(\tfrac{1}{\sqrt{\Delta t^N}}\Delta F^N_m\Big)\longrightarrow e^{\beta t}I_t$$
--   stably in law on $[0,T]$.
--
--   Combined with the explicit solution of the difference equation and control of the gap between $(1-\beta\Delta t^N)^{-m}$ and $e^{\beta t^N_m}$, this gives the convergence of $I^N$ itself.
--
--   **Formalization Note** The page writes "$\to$" with an unspecified $n$; it is read as stable convergence in law (as in Theorem A.3) with $n$ the number of grid steps up to $t$, $\lceil t/\Delta t^N\rceil\wedge N$. The growth bound on $g$ is the hypothesis added to Theorem 3.3 (Assumption A.2(c), p. 25). As in Theorem 3.3, the extension, $W'$ and $I$ are existential.
-- source:
--   Muhle-Karbe, Wang & Webster, Stochastic liquidity as a proxy for nonlinear price impact, SSRN 4286108 (version of November 2, 2023), p. 28, Appendix A.1, second step of the two-step procedure

import Mathlib
import Definitions.Def_PropagatorLimit_Scaling_Model

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace PropagatorLimit.Scaling

/-- Appendix A.1, p. 28: `√Δt^N Σ_{m=1}^{n} e^{β t^N_m} g(ΔF^N_m / √Δt^N) → e^{βt} I_t`, where `I`
is the linear price impact model of Theorem 3.3; `n = ⌈t/Δt^N⌉ ∧ N` and the arrow is stable
convergence in law on `[0, T]`. -/
theorem rescaled_convergence {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W Wperp : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianPair P 𝓕 W Wperp)
    (T : ℝ≥0) (hT : 0 < T) (fl : Flow Ω) (hfl : IsFlow P 𝓕 W Wperp T fl)
    (beta : ℝ) (hbeta : 0 < beta) (g : ℝ → ℝ) (hg : IsImpactFn g) :
    ∃ (E : Extension Ω P 𝓕) (Wp : ℝ≥0 → E.Ω' → ℝ) (I : ℝ≥0 → E.Ω' → ℝ),
      E.IsVeryGood ∧ IsFBrownian E.P' E.𝓖 Wp ∧
      EthierKurtz.HasCrossVariation E.P' (fun t ω' => W t (E.π ω')) Wp
        (fun t ω' => ∫ u in (0 : ℝ)..t.val, rho g (fl.v u.toNNReal (E.π ω'))) ∧
      SolvesLinearImpact beta g W fl E Wp I ∧
      StablyConverges P T
        (fun N ω t => Real.sqrt (dt T N) * ∑ m ∈ Finset.Icc 1 (nsteps T N t),
          Real.exp (beta * (m * dt T N)) * g (incr T N fl.F m ω / Real.sqrt (dt T N)))
        E (fun ω' t => Real.exp (beta * t) * I t ω') := by sorry

end PropagatorLimit.Scaling
